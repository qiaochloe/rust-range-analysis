//! Range analysis finds lower and upper bounds to the values that variables can assume. Currently
//! only operates on integer types.

// TODO: dead code elimination, array bounds checking elimination
// overflow check elimination, static branch prediction
// TODO: remove Integer from the name

// TODO: remove
#![allow(
    dead_code,
    unused_imports,
    unused_variables,
    unreachable_code,
    unused_mut,
    unreachable_pub
)]

use std::assert_matches::assert_matches;
use std::cell::RefCell;
use std::fmt::Formatter;

use rustc_abi::{BackendRepr, FIRST_VARIANT, FieldIdx, Size, VariantIdx};
use rustc_const_eval::const_eval::{DummyMachine, throw_machine_stop_str};
use rustc_const_eval::interpret::{
    ImmTy, Immediate, InterpCx, OpTy, PlaceTy, Projectable, interp_ok,
};
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def::DefKind;
use rustc_middle::bug;
use rustc_middle::mir::interpret::{InterpResult, Scalar};
use rustc_middle::mir::visit::{MutVisitor, PlaceContext, Visitor};
use rustc_middle::mir::*;
use rustc_middle::ty::{self, ScalarInt, Ty, TyCtxt};
use rustc_mir_dataflow::fmt::DebugWithContext;
use rustc_mir_dataflow::lattice::{FlatSet, HasBottom, HasTop};
use rustc_mir_dataflow::value_analysis::{
    Map, PlaceIndex, State, TrackElem, ValueOrPlace, debug_with_context,
};
use rustc_mir_dataflow::{Analysis, JoinSemiLattice, ResultsVisitor, visit_reachable_results};
use rustc_span::DUMMY_SP;
use tracing::{debug, debug_span, instrument};

use crate::patch::MirPatch;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Range {
    pub lo: ScalarInt,
    pub hi: ScalarInt,
    /// Whether the value is of a signed integer type.
    pub signed: bool,
}

impl Range {
    pub fn new(lo: ScalarInt, hi: ScalarInt, signed: bool) -> Self {
        Self { lo, hi, signed }
    }

    pub fn singleton(v: ScalarInt, signed: bool) -> Self {
        Range { lo: v, hi: v, signed }
    }

    fn compare(&self, a: ScalarInt, b: ScalarInt) -> std::cmp::Ordering {
        let size = a.size();
        if self.signed {
            a.to_int(size).cmp(&b.to_int(size))
        } else {
            a.to_uint(size).cmp(&b.to_uint(size))
        }
    }

    pub fn join(&self, other: &Self) -> Self {
        if self.signed != other.signed {
            bug!(
                "Cannot join ranges with different signedness: self.signed={}, other.signed={}",
                self.signed,
                other.signed
            );
        }

        let lo = if self.compare(self.lo, other.lo).is_le() { self.lo } else { other.lo };
        let hi = if self.compare(self.hi, other.hi).is_ge() { self.hi } else { other.hi };
        Range { lo, hi, signed: self.signed }
    }

    pub fn intersect(self, other: Self) -> Option<Self> {
        if self.signed != other.signed {
            bug!(
                "Cannot intersect ranges with different signedness: self.signed={}, other.signed={}",
                self.signed,
                other.signed
            );
        }

        let lo = if self.compare(self.lo, other.lo).is_ge() { self.lo } else { other.lo };
        let hi = if self.compare(self.hi, other.hi).is_le() { self.hi } else { other.hi };
        if self.compare(lo, hi).is_le() {
            Some(Range { lo, hi, signed: self.signed })
        } else {
            None
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RangeLattice {
    Bottom,
    Range(Range),
    Top,
}

impl JoinSemiLattice for RangeLattice {
    fn join(&mut self, other: &Self) -> bool {
        match (&*self, other) {
            (Self::Top, _) | (_, Self::Bottom) => false,
            (Self::Bottom, Self::Range(x)) => {
                *self = Self::Range(x.clone());
                true
            }
            (Self::Bottom, Self::Top) => {
                *self = Self::Top;
                true
            }
            (Self::Range(a), Self::Range(b)) if a == b => false,
            (Self::Range(a), Self::Range(b)) if a != b => {
                *self = Self::Range(a.join(b));
                true
            }
            (Self::Range(x), _) => false,
        }
    }
}

impl HasBottom for RangeLattice {
    const BOTTOM: Self = Self::Bottom;

    fn is_bottom(&self) -> bool {
        matches!(self, Self::Bottom)
    }
}

impl HasTop for RangeLattice {
    const TOP: Self = Self::Top;
}

pub(super) struct IntegerRange;

impl<'tcx> crate::MirPass<'tcx> for IntegerRange {
    fn is_enabled(&self, sess: &rustc_session::Session) -> bool {
        // TODO: change back to 3
        sess.mir_opt_level() >= 4
    }

    // fn name(&self) -> &'static str {
    //     const { simplify_pass_type_name(std::any::type_name::<Self>()) }
    // }

    // fn profiler_name(&self) -> &'static str {
    //     to_profiler_name(self.name())
    // }

    /// Returns `true` if this pass can be overridden by `-Zenable-mir-passes`. This should be
    /// true for basically every pass other than those that are necessary for correctness.
    fn can_be_overridden(&self) -> bool {
        // TODO:
        false
    }

    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        let place_limit = None;
        let map = Map::new(tcx, body, place_limit);

        let results = debug_span!("analyze").in_scope(|| {
            IntegerRangeAnalysis::new(tcx, body, map).iterate_to_fixpoint(tcx, body, None)
        });

        // let mut map = const_.analysis.map;
        // dbg!(&map);

        //let mut states = const_.entry_states;
        //dbg!(&states);

        // Perform dead code elimination based on range analysis
        let patch = {
            let mut visitor = Collector::new(tcx, body, &results);
            debug_span!("collect").in_scope(|| {
                visit_reachable_results(body, &results, &mut visitor);
            });
            visitor.patch
        };

        debug_span!("patch").in_scope(|| {
            patch.apply(body);
        });
    }

    // fn is_mir_dump_enabled(&self) -> bool {
    //     true
    // }

    /// Returns `true` if this pass must be run (i.e. it is required for soundness).
    /// For passes which are strictly optimizations, this should return `false`.
    /// If this is `false`, `#[optimize(none)]` will disable the pass.
    fn is_required(&self) -> bool {
        // TODO: change later
        true
    }
}

struct IntegerRangeAnalysis<'a, 'tcx> {
    map: Map<'tcx>,
    tcx: TyCtxt<'tcx>,
    local_decls: &'a LocalDecls<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
}

impl<'tcx> Analysis<'tcx> for IntegerRangeAnalysis<'_, 'tcx> {
    type Domain = State<RangeLattice>;

    const NAME: &'static str = "IntegerRangeAnalysis";

    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        State::Unreachable
    }

    fn initialize_start_block(&self, body: &Body<'tcx>, state: &mut Self::Domain) {
        // The initial state maps all tracked places of argument projections to ⊤ and the rest to ⊥.
        assert_matches!(state, State::Unreachable);
        *state = State::new_reachable();
        for arg in body.args_iter() {
            state.flood(PlaceRef { local: arg, projection: &[] }, &self.map);
        }
    }

    fn apply_primary_statement_effect(
        &self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        _location: Location,
    ) {
        if state.is_reachable() {
            self.handle_statement(statement, state);
        }
    }

    fn apply_primary_terminator_effect<'mir>(
        &self,
        state: &mut Self::Domain,
        terminator: &'mir Terminator<'tcx>,
        _location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        if state.is_reachable() {
            self.handle_terminator(terminator, state)
        } else {
            TerminatorEdges::None
        }
    }

    fn apply_call_return_effect(
        &self,
        state: &mut Self::Domain,
        _block: BasicBlock,
        return_places: CallReturnPlaces<'_, 'tcx>,
    ) {
        if state.is_reachable() {
            self.handle_call_return(return_places, state)
        }
    }
}

impl<'a, 'tcx> IntegerRangeAnalysis<'a, 'tcx> {
    fn new(tcx: TyCtxt<'tcx>, body: &'a Body<'tcx>, map: Map<'tcx>) -> Self {
        let typing_env = body.typing_env(tcx);
        Self { map, tcx, local_decls: &body.local_decls, typing_env }
    }

    fn handle_statement(&self, statement: &Statement<'tcx>, state: &mut State<RangeLattice>) {
        match &statement.kind {
            StatementKind::Assign(box (place, rvalue)) => {
                self.handle_assign(*place, rvalue, state);
            }
            StatementKind::SetDiscriminant { box place, variant_index } => {
                self.handle_set_discriminant(*place, *variant_index, state);
            }
            StatementKind::Intrinsic(box intrinsic) => {
                self.handle_intrinsic(intrinsic);
            }
            StatementKind::StorageLive(local) | StatementKind::StorageDead(local) => {
                // StorageLive leaves the local in an uninitialized state
                // StorageDead makes it UB to access the local afterwards
                state.flood_with(Place::from(*local).as_ref(), &self.map, RangeLattice::BOTTOM);
            }
            StatementKind::Retag(..) => {
                // We don't track references.
            }
            StatementKind::ConstEvalCounter
            | StatementKind::Nop
            | StatementKind::FakeRead(..)
            | StatementKind::PlaceMention(..)
            | StatementKind::Coverage(..)
            | StatementKind::BackwardIncompatibleDropHint { .. }
            | StatementKind::AscribeUserType(..) => {}
        }
    }

    fn handle_intrinsic(&self, intrinsic: &NonDivergingIntrinsic<'tcx>) {
        match intrinsic {
            NonDivergingIntrinsic::Assume(..) => {
                // Could use this, but ignoring it is sound.
            }
            NonDivergingIntrinsic::CopyNonOverlapping(CopyNonOverlapping {
                dst: _,
                src: _,
                count: _,
            }) => {
                // This statement represents `*dst = *src`, `count` times.
            }
        }
    }

    fn handle_assign(
        &self,
        target: Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
        state: &mut State<RangeLattice>,
    ) {
        match rvalue {
            Rvalue::Use(operand) => {
                state.flood(target.as_ref(), &self.map);
                if let Some(target_idx) = self.map.find(target.as_ref()) {
                    self.assign_operand(state, target_idx, operand);
                }
            }

            Rvalue::CopyForDeref(_) => bug!("`CopyForDeref` in runtime MIR"),

            Rvalue::Aggregate(..) => {
                // todo!();
            }

            Rvalue::BinaryOp(op, box (left, right)) if op.is_overflowing() => {
                // todo!();
            }

            Rvalue::Cast(
                CastKind::PointerCoercion(ty::adjustment::PointerCoercion::Unsize, _),
                operand,
                _,
            ) => {
                // todo!()
            }
            _ => {
                let result = self.handle_rvalue(rvalue, state);
                state.assign(target.as_ref(), result, &self.map);
            }
        }
    }

    fn handle_rvalue(
        &self,
        rvalue: &Rvalue<'tcx>,
        state: &mut State<RangeLattice>,
    ) -> ValueOrPlace<RangeLattice> {
        let val = match rvalue {
            Rvalue::Cast(CastKind::IntToInt | CastKind::IntToFloat, operand, ty) => {
                // TODO:
                RangeLattice::Top
            }

            Rvalue::Cast(CastKind::FloatToInt | CastKind::FloatToFloat, operand_, ty_) => {
                RangeLattice::Top
            }

            Rvalue::Cast(CastKind::Transmute | CastKind::Subtype, operand, ty) => {
                // TODO: need to handle wrap_immediate
                self.eval_operand(operand, state)
            }

            Rvalue::BinaryOp(op, box (left, right)) if !op.is_overflowing() => {
                // Overflows must be ignored here.
                // The overflowing operators are handled in `handle_assign`.
                let (val, _overflow) = self.binary_op(state, *op, left, right);
                val
            }

            Rvalue::UnaryOp(_, operand) => {
                // TODO:
                self.eval_operand(operand, state)
            }

            Rvalue::NullaryOp(NullOp::RuntimeChecks(_)) => {
                return ValueOrPlace::TOP;
            }

            Rvalue::Discriminant(place) => {
                RangeLattice::Top
                // state.get_discr(place.as_ref(), &self.map)
            }

            Rvalue::Use(operand) => return self.handle_operand(operand, state),

            Rvalue::CopyForDeref(_) => bug!("`CopyForDeref` in runtime MIR"),

            Rvalue::ShallowInitBox(..) => bug!("`ShallowInitBox` in runtime MIR"),

            Rvalue::Ref(..) | Rvalue::RawPtr(..) => {
                // We do not track pointer ranges in this analysis.
                return ValueOrPlace::TOP;
            }
            Rvalue::Repeat(..)
            | Rvalue::ThreadLocalRef(..)
            | Rvalue::Cast(..)
            | Rvalue::BinaryOp(..)
            | Rvalue::Aggregate(..)
            | Rvalue::WrapUnsafeBinder(..) => {
                // No modification is possible through these r-values.
                return ValueOrPlace::TOP;
            }
        };
        ValueOrPlace::Value(val)
    }

    fn handle_operand(
        &self,
        operand: &Operand<'tcx>,
        state: &mut State<RangeLattice>,
    ) -> ValueOrPlace<RangeLattice> {
        match operand {
            Operand::Constant(box constant) => {
                ValueOrPlace::Value(self.handle_constant(constant, state))
            }
            Operand::Copy(place) | Operand::Move(place) => {
                // On move, we would ideally flood the place with bottom. But with the current
                // framework this is not possible (similar to `InterpCx::eval_operand`).
                self.map.find(place.as_ref()).map(ValueOrPlace::Place).unwrap_or(ValueOrPlace::TOP)
            }
        }
    }

    fn handle_terminator<'mir>(
        &self,
        terminator: &'mir Terminator<'tcx>,
        state: &mut State<RangeLattice>,
    ) -> TerminatorEdges<'mir, 'tcx> {
        match &terminator.kind {
            TerminatorKind::Call { .. } | TerminatorKind::InlineAsm { .. } => {
                // Return handled in `handle_call_return`.
            }
            TerminatorKind::Drop { place, .. } => {
                state.flood_with(place.as_ref(), &self.map, RangeLattice::BOTTOM);
            }
            TerminatorKind::Yield { .. } => {
                // They would have an effect, but are not allowed in this phase.
                bug!("encountered disallowed terminator");
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                return self.handle_switch_int(discr, targets, state);
            }
            TerminatorKind::TailCall { .. }
            | TerminatorKind::Goto { .. }
            | TerminatorKind::UnwindResume
            | TerminatorKind::UnwindTerminate(_)
            | TerminatorKind::Return
            | TerminatorKind::Unreachable
            | TerminatorKind::Assert { .. }
            | TerminatorKind::CoroutineDrop
            | TerminatorKind::FalseEdge { .. }
            | TerminatorKind::FalseUnwind { .. } => {
                // These terminators have no effect on the analysis.
                // TODO: check if that is true
            }
        }
        terminator.edges()
    }

    fn handle_call_return(
        &self,
        return_places: CallReturnPlaces<'_, 'tcx>,
        state: &mut State<RangeLattice>,
    ) {
        // TODO: not interprocedural yet
        return_places.for_each(|place| {
            state.flood(place.as_ref(), &self.map);
        })
    }

    fn handle_constant(
        &self,
        constant: &ConstOperand<'tcx>,
        _state: &mut State<RangeLattice>,
    ) -> RangeLattice {
        let ty = constant.const_.ty();
        if !ty.is_integral() {
            return RangeLattice::Top;
        }
        let signed = ty.is_signed();
        match constant.const_.try_eval_scalar_int(self.tcx, self.typing_env) {
            Some(scalar_int) => RangeLattice::Range(Range::singleton(scalar_int, signed)),
            None => RangeLattice::Top,
        }
    }

    /// Returns val and overflow
    fn binary_op(
        &self,
        state: &mut State<RangeLattice>,
        op: BinOp,
        left: &Operand<'tcx>,
        right: &Operand<'tcx>,
    ) -> (RangeLattice, RangeLattice) {
        let llat = self.eval_operand(left, state);
        let rlat = self.eval_operand(right, state);
        match (llat, rlat) {
            (RangeLattice::Bottom, _) | (_, RangeLattice::Bottom) => {
                (RangeLattice::Bottom, RangeLattice::Bottom)
            }

            // Both sides are known, do the actual computation.
            (RangeLattice::Range(l), RangeLattice::Range(r)) => {
                let ty = left.ty(self.local_decls, self.tcx);
                if !ty.is_integral() {
                    return (RangeLattice::Top, RangeLattice::Top);
                }
                let Ok(layout) = self.tcx.layout_of(self.typing_env.as_query_input(ty)) else {
                    return (RangeLattice::Top, RangeLattice::Top);
                };
                let size = layout.size;
                let signed = ty.is_signed();

                use BinOp::*;
                let res = match op {
                    Add | Sub | Mul => self.arith_interval(op, l, r, size, signed),
                    BitAnd | BitOr | BitXor => self.bitwise_interval(op, l, r, size),
                    Shl | Shr => self.shift_interval(op, l, r, size, signed),
                    Eq | Ne | Lt | Le | Gt | Ge => {
                        self.bool_interval_from_compare(op, l, r, size, signed)
                    }
                    _ => return (RangeLattice::Top, RangeLattice::Top),
                };

                (res, res)
            }

            // Exactly one side is known, attempt some algebraic simplifications.
            (RangeLattice::Range(const_arg), _) | (_, RangeLattice::Range(const_arg)) => {
                // TODO:
                return (RangeLattice::Top, RangeLattice::Top);
                // let layout = const_arg.layout;
                // if !matches!(layout.backend_repr, rustc_abi::BackendRepr::Scalar(..)) {
                //     return (RangeLattice::Top, RangeLattice::Top);
                // }
                //
                // let arg_scalar = const_arg.to_scalar();
                // let Some(arg_value) = arg_scalar.to_bits(layout.size).discard_err() else {
                //     return (RangeLattice::Top, RangeLattice::Top);
                // };
                //
                // match op {
                //     BinOp::BitAnd if arg_value == 0 => (RangeLattice::Range(arg_scalar), RangeLattice::Bottom),
                //     BinOp::BitOr
                //         if arg_value == layout.size.truncate(u128::MAX)
                //             || (layout.ty.is_bool() && arg_value == 1) =>
                //     {
                //         (RangeLattice::Range(arg_scalar), RangeLattice::Bottom)
                //     }
                //     BinOp::Mul if layout.ty.is_integral() && arg_value == 0 => {
                //         (RangeLattice::Range(arg_scalar), RangeLattice::Range(Scalar::from_bool(false)))
                //     }
                //     _ => (RangeLattice::Top, RangeLattice::Top),
                // }
            }
            (RangeLattice::Top, RangeLattice::Top) => (RangeLattice::Top, RangeLattice::Top),
        }
    }

    fn arith_interval(
        &self,
        op: BinOp,
        l: Range,
        r: Range,
        size: Size,
        signed: bool,
    ) -> RangeLattice {
        // TODO: should we use std in the compiler?
        use std::cmp::{max, min};

        use BinOp::*;

        // TODO: is this conversion from u128 to i128 safe? What if there is overflow
        let to_i = |s: ScalarInt| -> i128 {
            if signed { s.to_int(size) } else { s.to_uint(size) as i128 }
        };

        let from_i = |v: i128| -> ScalarInt {
            if signed { ScalarInt::from(v) } else { ScalarInt::from(v as u128) }
        };

        let ll = to_i(l.lo);
        let lh = to_i(l.hi);
        let rl = to_i(r.lo);
        let rh = to_i(r.hi);

        let (min_v, max_v) = match op {
            Add => (ll + rl, lh + rh),
            Sub => (ll - rh, lh - rl),
            Mul => {
                let candidates = [ll * rl, ll * rh, lh * rl, lh * rh];
                let &mn = candidates.iter().min().unwrap();
                let &mx = candidates.iter().max().unwrap();
                (mn, mx)
            }
            _ => unreachable!(),
        };

        let res_lo = from_i(min_v);
        let res_hi = from_i(max_v);
        RangeLattice::Range(Range::new(res_lo, res_hi, signed))
    }

    fn bitwise_interval(&self, op: BinOp, l: Range, r: Range, size: Size) -> RangeLattice {
        use std::cmp::{max, min};

        use BinOp::*;

        // TODO: only implemented for unsigned ints
        // Bitwise operations are typically unsigned, but we preserve the signedness from input ranges
        let signed = l.signed; // Both ranges should have same signedness

        let to_u = |s: ScalarInt| -> u128 { s.to_uint(size) };

        let from_u = |v: u128| -> ScalarInt {
            let truncated = size.truncate(v);
            ScalarInt::try_from_uint(truncated, size).unwrap()
        };

        match op {
            BitAnd => {
                if l.lo == l.hi && r.lo == r.hi {
                    let res = from_u(to_u(l.lo) & to_u(r.lo));
                    return RangeLattice::Range(Range::singleton(res, signed));
                }

                // 0 <= (a & b) <= min(a, b)
                let l_hi = to_u(l.hi);
                let r_hi = to_u(r.hi);
                let hi = from_u(l_hi.min(r_hi));
                let lo = from_u(0);

                RangeLattice::Range(Range::new(lo, hi, signed))
            }

            BitOr => {
                if l.lo == l.hi && r.lo == r.hi {
                    let res = from_u(to_u(l.lo) | to_u(r.lo));
                    return RangeLattice::Range(Range::singleton(res, signed));
                }

                // min >= max(lo_l, lo_r)
                // max <= hi_l | hi_r.
                let l_lo = to_u(l.lo);
                let r_lo = to_u(r.lo);
                let l_hi = to_u(l.hi);
                let r_hi = to_u(r.hi);

                let lo = from_u(l_lo.max(r_lo));
                let hi = from_u(l_hi | r_hi);

                RangeLattice::Range(Range::new(lo, hi, signed))
            }

            BitXor => {
                if l.lo == l.hi && r.lo == r.hi {
                    let res = from_u(to_u(l.lo) ^ to_u(r.lo));
                    return RangeLattice::Range(Range::singleton(res, signed));
                }

                let mask = size.truncate(u128::MAX);
                let lo = from_u(0);
                let hi = from_u(mask);
                RangeLattice::Range(Range::new(lo, hi, signed))
            }
            _ => unreachable!(),
        }
    }

    fn shift_interval(
        &self,
        _op: BinOp,
        _l: Range,
        _r: Range,
        _size: Size,
        _signed: bool,
    ) -> RangeLattice {
        todo!();
    }

    fn bool_interval_from_compare(
        &self,
        op: BinOp,
        l: Range,
        r: Range,
        size: Size,
        signed: bool,
    ) -> RangeLattice {
        use BinOp::*;

        let to_i = |s: ScalarInt| -> i128 {
            if signed { s.to_int(size) } else { s.to_uint(size) as i128 }
        };

        let ll = to_i(l.lo);
        let lh = to_i(l.hi);
        let rl = to_i(r.lo);
        let rh = to_i(r.hi);

        let make_bool_range = |always_true: bool,
                               always_false: bool,
                               this: &IntegerRangeAnalysis<'_, '_>| {
            // Get the layout of `bool` to size the ScalarInt correctly.
            let layout = this
                .tcx
                .layout_of(this.typing_env.as_query_input(this.tcx.types.bool))
                .expect("bool layout must exist");
            let size = layout.size;

            let mk_scalar = |v: u128| {
                ScalarInt::try_from_uint(size.truncate(v), size).expect("bool scalar should fit")
            };

            let zero = mk_scalar(0);
            let one = mk_scalar(1);
            let signed = false;

            if always_true && !always_false {
                RangeLattice::Range(Range::singleton(one, signed))
            } else if always_false && !always_true {
                RangeLattice::Range(Range::singleton(zero, signed))
            } else {
                RangeLattice::Range(Range::new(zero, one, signed))
            }
        };

        let (always_true, always_false) = match op {
            Eq => {
                let disjoint = lh < rl || rh < ll;
                let singleton_equal = ll == lh && rl == rh && ll == rl;
                (singleton_equal, disjoint)
            }

            Ne => {
                let disjoint = lh < rl || rh < ll;
                let singleton_equal = ll == lh && rl == rh && ll == rl;
                (disjoint, singleton_equal)
            }

            Lt => {
                let always_true = lh < rl;
                let always_false = ll >= rh;
                (always_true, always_false)
            }

            Le => {
                let always_true = lh <= rl;
                let always_false = ll > rh;
                (always_true, always_false)
            }

            Gt => {
                let always_true = rh < ll;
                let always_false = rl >= lh;
                (always_true, always_false)
            }

            Ge => {
                let always_true = rh <= ll;
                let always_false = rl > lh;
                (always_true, always_false)
            }
            _ => unreachable!(""),
        };

        make_bool_range(always_true, always_false, self)
    }

    fn handle_switch_int<'mir>(
        &self,
        discr: &'mir Operand<'tcx>,
        targets: &'mir SwitchTargets,
        state: &mut State<RangeLattice>,
    ) -> TerminatorEdges<'mir, 'tcx> {
        // FIXME:
        let value = match self.handle_operand(discr, state) {
            ValueOrPlace::Value(value) => value,
            ValueOrPlace::Place(place) => state.get_idx(place, &self.map),
        };

        match value {
            RangeLattice::Bottom => TerminatorEdges::None,
            RangeLattice::Top => TerminatorEdges::SwitchInt { discr, targets },

            RangeLattice::Range(Range { lo, hi, .. }) => {
                // TODO: filter out more

                // If the range is a singleton && it matches exactly one target,
                // we can choose a single edge. Otherwise, keep it symbolic.
                if lo == hi {
                    let bits = lo.to_bits_unchecked();
                    let target = targets.target_for_value(bits);
                    TerminatorEdges::Single(target)
                } else {
                    TerminatorEdges::SwitchInt { discr, targets }
                }
            }
        }
    }

    /// The caller must have flooded `place`.
    fn assign_operand(
        &self,
        state: &mut State<RangeLattice>,
        place: PlaceIndex,
        operand: &Operand<'tcx>,
    ) {
        match operand {
            Operand::Copy(rhs) | Operand::Move(rhs) => {
                if let Some(rhs_idx) = self.map.find(rhs.as_ref()) {
                    state.insert_place_idx(place, rhs_idx, &self.map);
                } else {
                    // Untracked place => Top.
                    state.insert_value_idx(place, RangeLattice::Top, &self.map);
                }
            }
            Operand::Constant(box constant) => {
                // Direct constant assignment.
                let val = self.handle_constant(constant, state);
                state.insert_value_idx(place, val, &self.map);
            }
        }
    }

    /// The caller must have flooded `place`.
    fn assign_constant(
        &self,
        state: &mut State<RangeLattice>,
        place: PlaceIndex,
        mut operand: OpTy<'tcx>,
        projection: &[PlaceElem<'tcx>],
    ) {
        todo!();
    }

    fn eval_operand(&self, op: &Operand<'tcx>, state: &mut State<RangeLattice>) -> RangeLattice {
        // WARNING: might need to handle more values
        let value = match self.handle_operand(op, state) {
            ValueOrPlace::Value(value) => value,
            ValueOrPlace::Place(place) => state.get_idx(place, &self.map),
        };
        value
    }

    fn handle_set_discriminant(
        &self,
        place: Place<'tcx>,
        variant_index: VariantIdx,
        state: &mut State<RangeLattice>,
    ) {
        todo!();
    }

    fn eval_discriminant(&self, enum_ty: Ty<'tcx>, variant_index: VariantIdx) -> Option<Scalar> {
        todo!();
    }

    fn wrap_immediate(&self, imm: Immediate) -> RangeLattice {
        match imm {
            Immediate::Scalar(Scalar::Int(v)) => {
                // FIXME:
                // Default to unsigned if we don't have type information
                // This is used in contexts where type info might not be available
                RangeLattice::Range(Range::singleton(v, false))
            }
            Immediate::Uninit => RangeLattice::Bottom,
            _ => RangeLattice::Top,
        }
    }
}

/// This is used to visualize the dataflow analysis.
impl<'tcx> DebugWithContext<IntegerRangeAnalysis<'_, 'tcx>> for State<RangeLattice> {
    fn fmt_with(
        &self,
        ctxt: &IntegerRangeAnalysis<'_, 'tcx>,
        f: &mut Formatter<'_>,
    ) -> std::fmt::Result {
        match self {
            State::Reachable(values) => debug_with_context(values, None, &ctxt.map, f),
            State::Unreachable => write!(f, "unreachable"),
        }
    }

    fn fmt_diff_with(
        &self,
        old: &Self,
        ctxt: &IntegerRangeAnalysis<'_, 'tcx>,
        f: &mut Formatter<'_>,
    ) -> std::fmt::Result {
        match (self, old) {
            (State::Reachable(this), State::Reachable(old)) => {
                debug_with_context(this, Some(old), &ctxt.map, f)
            }
            _ => Ok(()),
        }
    }
}

/// Helper methods for dead code elimination
impl<'a, 'tcx> IntegerRangeAnalysis<'a, 'tcx> {
    /// Evaluates a boolean operand.
    /// Returns Some(true) if always true, Some(false) if always false, None if unknown.
    fn eval_bool(&self, operand: &Operand<'tcx>, state: &State<RangeLattice>) -> Option<bool> {
        if !state.is_reachable() {
            return None;
        }

        let ty = operand.ty(self.local_decls, self.tcx);
        if !ty.is_bool() {
            return None;
        }

        let mut state_mut = state.clone();
        let value = self.eval_operand(operand, &mut state_mut);
        match value {
            RangeLattice::Bottom => None,
            RangeLattice::Top => None,
            RangeLattice::Range(Range { lo, hi, .. }) => {
                let lo_bits = lo.to_bits_unchecked();
                let hi_bits = hi.to_bits_unchecked();
                assert!(lo_bits == 0 || lo_bits == 1);
                assert!(hi_bits == 0 || hi_bits == 1);

                if lo == hi {
                    if lo_bits == 0 {
                        return Some(false);
                    } else if lo_bits == 1 {
                        return Some(true);
                    }
                }
                None
            }
        }
    }
}

struct Collector<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    analysis: &'a IntegerRangeAnalysis<'a, 'tcx>,
    patch: MirPatch<'tcx>,
}

impl<'a, 'tcx> Collector<'a, 'tcx> {
    fn new(
        tcx: TyCtxt<'tcx>,
        body: &'a Body<'tcx>,
        results: &'a rustc_mir_dataflow::Results<'tcx, IntegerRangeAnalysis<'a, 'tcx>>,
    ) -> Self {
        Self { tcx, body, analysis: &results.analysis, patch: MirPatch::new(body) }
    }
}

impl<'a, 'tcx> ResultsVisitor<'tcx, IntegerRangeAnalysis<'a, 'tcx>> for Collector<'a, 'tcx> {
    fn visit_after_primary_terminator_effect(
        &mut self,
        _analysis: &IntegerRangeAnalysis<'a, 'tcx>,
        state: &State<RangeLattice>,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) {
        match &terminator.kind {
            TerminatorKind::Assert { cond, expected, target, unwind, msg } => {
                // Try to evaluate the condition using range analysis
                let cond_value = self.analysis.eval_bool(cond, state);

                if let Some(always_true) = cond_value {
                    // Assert always succeeds, replace with goto
                    if always_true == *expected {
                        self.patch.patch_terminator(
                            location.block,
                            TerminatorKind::Goto { target: *target },
                        );
                    } else {
                        // Assert always fails, replace with unreachable
                        self.patch.patch_terminator(location.block, TerminatorKind::Unreachable);
                    }
                }
            }

            TerminatorKind::SwitchInt { discr, targets } => {
                // First, check if we can evaluate the discriminant to a singleton range
                let mut state_mut = state.clone();
                let value = self.analysis.eval_operand(discr, &mut state_mut);

                if let RangeLattice::Range(Range { lo, hi, .. }) = value {
                    // Handle singleton range
                    if lo == hi {
                        let bits = lo.to_bits_unchecked();
                        let target = targets.target_for_value(bits);
                        self.patch
                            .patch_terminator(location.block, TerminatorKind::Goto { target });
                        return;
                    }

                    let lo_bits = lo.to_bits_unchecked();
                    let hi_bits = hi.to_bits_unchecked();

                    let filtered: Vec<_> = targets
                        .iter()
                        .filter(|(value, _)| *value >= lo_bits && *value <= hi_bits)
                        .collect();

                    let original_count = targets.iter().count();
                    let num_explicit_targets = filtered.len();

                    // If only one target is possible, simplify to goto
                    if num_explicit_targets == 0 {
                        let otherwise = targets.otherwise();
                        self.patch.patch_terminator(
                            location.block,
                            TerminatorKind::Goto { target: otherwise },
                        );
                    } else if num_explicit_targets < original_count {
                        // Multiple targets, but some were filtered
                        let otherwise = targets.otherwise();
                        let filtered_targets = SwitchTargets::new(filtered.into_iter(), otherwise);
                        self.patch.patch_terminator(
                            location.block,
                            TerminatorKind::SwitchInt {
                                discr: discr.clone(),
                                targets: filtered_targets,
                            },
                        );
                    }
                }
            }
            _ => {}
        }
    }
}
