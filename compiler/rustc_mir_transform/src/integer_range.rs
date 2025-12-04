//! Range analysis finds lower and upper bounds to the values that variables can assume.

// NOTE: can implement array bounds checking elimination, overflow check elimination, static branch prediction
// FIXME: remove Integer from the name

// FIXME:
// handle AddWithOverflow and SubWithOverflow
// handle indexing operations
// handle cast operations
// char to int conversions
// handle isize and usize
// only u8 can be cast as char
// char can be cast to u32
// handle infinite loops, widening and lowering

// FIXME: test casting

/* TESTS

NOT OPTIMIZING:
COMPARISON_OPS
CONTROL_FLOW
RANGE_INTERSECTION
SWITCH_INT_OPT

PASSING:
binary_ops
bool_u8_cast (can be more aggressive wtih match)
constant_prop
int_to_int_cast
simple_division

FAILING TO COMPILE:
nested_loops
widening
*/
// - assert_opt doesn't optimize out the assert
// - comparison_ops doesn't optimize out the assert
// - switch_int_opt doesn't optimize out the match
// - shift_ops has an unrelated can't convert to uint bug

// FIXME: can't handle control flow
// e.g. if x < 10 { assert!(x < 10) };

// FIXME: check to_i(|s: ScalarInt| -> i128 { s.to_int(s.size()) });
// whether we should use s.size() or size

// FIXME: remove
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
        sess.mir_opt_level() >= 3
    }

    /// Returns `true` if this pass can be overridden by `-Zenable-mir-passes`
    fn can_be_overridden(&self) -> bool {
        true
    }

    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        let place_limit = None;
        let map = Map::new(tcx, body, place_limit);

        let results = debug_span!("analyze").in_scope(|| {
            IntegerRangeAnalysis::new(tcx, body, map).iterate_to_fixpoint(tcx, body, None)
        });

        dbg!(&results.analysis.map);
        dbg!(&results.entry_states);

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

    /// If this is `false`, `#[optimize(none)]` will disable the pass.
    fn is_required(&self) -> bool {
        false
    }
}

struct IntegerRangeAnalysis<'a, 'tcx> {
    map: Map<'tcx>,
    tcx: TyCtxt<'tcx>,
    local_decls: &'a LocalDecls<'tcx>,
    ecx: RefCell<InterpCx<'tcx, DummyMachine>>,
    typing_env: ty::TypingEnv<'tcx>,
}

impl<'tcx> Analysis<'tcx> for IntegerRangeAnalysis<'_, 'tcx> {
    type Domain = State<RangeLattice>;

    const NAME: &'static str = "IntegerRangeAnalysis";

    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        State::Unreachable
    }

    fn initialize_start_block(&self, body: &Body<'tcx>, state: &mut Self::Domain) {
        assert_matches!(state, State::Unreachable);
        *state = State::new_reachable();
        for arg in body.args_iter() {
            let arg_ty = self.local_decls[arg].ty;
            let place_ref = PlaceRef { local: arg, projection: &[] };
            let type_range = self.get_type_range(arg_ty);
            if let Some(type_range) = type_range {
                state.assign(
                    place_ref,
                    ValueOrPlace::Value(RangeLattice::Range(type_range)),
                    &self.map,
                );
            } else {
                state.flood(place_ref, &self.map);
            }
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
        Self {
            map,
            tcx,
            local_decls: &body.local_decls,
            ecx: RefCell::new(InterpCx::new(tcx, DUMMY_SP, typing_env, DummyMachine)),
            typing_env,
        }
    }

    /// Get the valid range for a type.
    /// Returns None if the type is not integral or bool.
    fn get_type_range(&self, ty: Ty<'tcx>) -> Option<Range> {
        if ty.is_bool() {
            Some(Range::new(ScalarInt::FALSE, ScalarInt::TRUE, false))
        } else if ty.is_integral() {
            let signed = ty.is_signed();

            let Ok(layout) = self.tcx.layout_of(self.typing_env.as_query_input(ty)) else {
                return None;
            };
            let size = layout.size;

            let (type_min, type_max) = if signed {
                let signed_min = size.signed_int_min();
                let signed_max = size.signed_int_max();
                (
                    ScalarInt::try_from_int(signed_min, size).unwrap(),
                    ScalarInt::try_from_int(signed_max, size).unwrap(),
                )
            } else {
                let zero = ScalarInt::try_from_uint(0u128, size).unwrap();
                let unsigned_max = size.unsigned_int_max();
                let max = ScalarInt::try_from_uint(unsigned_max, size).unwrap();
                (zero, max)
            };
            Some(Range::new(type_min, type_max, signed))
        } else {
            None
        }
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

            Rvalue::Aggregate(kind, operands) => {
                // Flood the target place
                state.flood(target.as_ref(), &self.map);

                let Some(target_idx) = self.map.find(target.as_ref()) else { return };

                // Assign each field operand to the corresponding field
                let variant_target = match **kind {
                    AggregateKind::Tuple | AggregateKind::Closure(..) => Some(target_idx),
                    AggregateKind::Adt(def_id, variant_index, ..) => {
                        match self.tcx.def_kind(def_id) {
                            DefKind::Struct => Some(target_idx),
                            DefKind::Enum => {
                                // Track the variant-specific fields
                                self.map.apply(target_idx, TrackElem::Variant(variant_index))
                            }
                            _ => return,
                        }
                    }
                    _ => return,
                };

                if let Some(variant_target_idx) = variant_target {
                    // Assign each field operand to the corresponding field
                    for (field_index, operand) in operands.iter_enumerated() {
                        let operand_ty = operand.ty(self.local_decls, self.tcx);
                        if operand_ty.is_integral() {
                            if let Some(field) =
                                self.map.apply(variant_target_idx, TrackElem::Field(field_index))
                            {
                                self.assign_operand(state, field, operand);
                            }
                        }
                    }
                }
            }

            Rvalue::BinaryOp(op, box (left, right)) if op.is_overflowing() => {
                // FIXME: check, taken from dataflow_const_prop.rs
                state.flood(target.as_ref(), &self.map);

                let Some(target) = self.map.find(target.as_ref()) else { return };

                let value_target = self.map.apply(target, TrackElem::Field(0_u32.into()));
                let overflow_target = self.map.apply(target, TrackElem::Field(1_u32.into()));

                if value_target.is_some() || overflow_target.is_some() {
                    let (val, overflow) = self.binary_op(state, *op, left, right);

                    if let Some(value_target) = value_target {
                        // We have flooded `target` earlier.
                        state.insert_value_idx(value_target, val, &self.map);
                    }
                    if let Some(overflow_target) = overflow_target {
                        // We have flooded `target` earlier.
                        state.insert_value_idx(overflow_target, overflow, &self.map);
                    }
                }
            }

            Rvalue::Cast(
                CastKind::PointerCoercion(ty::adjustment::PointerCoercion::Unsize, _),
                operand,
                _,
            ) => {
                // FIXME: handle pointer coercions
                state.flood(target.as_ref(), &self.map);
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
            Rvalue::Cast(CastKind::IntToInt, operand, ty) => {
                // Only handle integral or bool types
                // FIXME: handle char?
                let operand_ty = operand.ty(self.local_decls, self.tcx);
                if !operand_ty.is_integral() && !operand_ty.is_bool() {
                    return ValueOrPlace::Value(RangeLattice::Top);
                }
                if !ty.is_integral() && !ty.is_bool() {
                    return ValueOrPlace::Value(RangeLattice::Top);
                }

                // Get layouts
                let Ok(operand_layout) =
                    self.tcx.layout_of(self.typing_env.as_query_input(operand_ty))
                else {
                    return ValueOrPlace::Value(RangeLattice::Top);
                };
                let Ok(target_layout) = self.tcx.layout_of(self.typing_env.as_query_input(*ty))
                else {
                    return ValueOrPlace::Value(RangeLattice::Top);
                };

                // Get the target type's full range
                let Some(type_range) = self.get_type_range(*ty) else {
                    return ValueOrPlace::Value(RangeLattice::Top);
                };

                match self.eval_operand(operand, state) {
                    RangeLattice::Range(range) => {
                        let target_signed = ty.is_signed();
                        let convert_bound = |bound: ScalarInt| -> ScalarInt {
                            let imm_ty = ImmTy::from_scalar_int(bound, operand_layout);
                            let result_imm_ty = self
                                .ecx
                                .borrow_mut()
                                .int_to_int_or_float(&imm_ty, target_layout)
                                .unwrap();
                            match *result_imm_ty {
                                Immediate::Scalar(Scalar::Int(v)) => v,
                                _ => bug!(
                                    "int_to_int_or_float returned non-integer for IntToInt cast"
                                ),
                            }
                        };

                        let lo = convert_bound(range.lo);
                        let hi = convert_bound(range.hi);

                        // Check if the source range is large enough to wrap around
                        // Calculate the width of the source range
                        let source_width = if range.signed {
                            let lo_val = range.lo.to_int(operand_layout.size);
                            let hi_val = range.hi.to_int(operand_layout.size);
                            (hi_val - lo_val) as u128 + 1
                        } else {
                            let lo_val = range.lo.to_uint(operand_layout.size);
                            let hi_val = range.hi.to_uint(operand_layout.size);
                            hi_val - lo_val + 1
                        };

                        // Number of distinct values in the target type
                        let target_num_values = target_layout.size.unsigned_int_max() + 1;

                        // Check if range wraps: if hi < lo after conversion, or if
                        // the source range is large enough to cover all target values
                        let wraps = if target_signed {
                            let lo_val = lo.to_int(target_layout.size);
                            let hi_val = hi.to_int(target_layout.size);
                            hi_val < lo_val || source_width > target_num_values
                        } else {
                            let lo_val = lo.to_uint(target_layout.size);
                            let hi_val = hi.to_uint(target_layout.size);
                            hi_val < lo_val || source_width > target_num_values
                        };

                        if wraps {
                            RangeLattice::Range(type_range)
                        } else {
                            let converted_range = Range::new(lo, hi, target_signed);
                            converted_range
                                .intersect(type_range)
                                .map(RangeLattice::Range)
                                .unwrap_or(RangeLattice::Top)
                        }
                    }
                    RangeLattice::Bottom => RangeLattice::Bottom,
                    RangeLattice::Top => {
                        // If operand is Top, check if we can at least provide the target type's range
                        self.get_type_range(*ty)
                            .map(RangeLattice::Range)
                            .unwrap_or(RangeLattice::Top)
                    }
                }
            }

            Rvalue::Cast(CastKind::IntToFloat, _operand, _ty) => {
                // Float ranges are not tracked, so return Top
                RangeLattice::Top
            }

            Rvalue::Cast(CastKind::FloatToInt, _operand, ty) => {
                // Return the target type's range
                self.get_type_range(*ty).map(RangeLattice::Range).unwrap_or(RangeLattice::Top)
            }

            Rvalue::Cast(CastKind::FloatToFloat, _operand, _ty) => {
                // Float ranges are not tracked, so return Top
                RangeLattice::Top
            }

            Rvalue::Cast(CastKind::Transmute | CastKind::Subtype, operand, ty) => {
                // FIXME: handle transmute/subtype
                RangeLattice::Top
            }

            Rvalue::BinaryOp(op, box (left, right)) if !op.is_overflowing() => {
                // Overflows must be ignored here.
                // The overflowing operators are handled in `handle_assign`.
                let (val, _overflow) = self.binary_op(state, *op, left, right);
                val
            }

            Rvalue::UnaryOp(_, operand) => {
                // FIXME:
                self.eval_operand(operand, state)
            }

            Rvalue::NullaryOp(NullOp::RuntimeChecks(_)) => {
                // FIXME:
                RangeLattice::Top
            }

            Rvalue::Discriminant(place) => {
                RangeLattice::Top
                // state.get_discr(place.as_ref(), &self.map)
            }

            Rvalue::Use(operand) => {
                return self.handle_operand(operand, state);
            }

            Rvalue::CopyForDeref(_) => bug!("`CopyForDeref` in runtime MIR"),

            Rvalue::ShallowInitBox(..) => bug!("`ShallowInitBox` in runtime MIR"),

            Rvalue::Ref(..) | Rvalue::RawPtr(..) => {
                // We do not track pointer ranges in this analysis.
                RangeLattice::Top
            }
            Rvalue::Repeat(..)
            | Rvalue::ThreadLocalRef(..)
            | Rvalue::Cast(..)
            | Rvalue::BinaryOp(..)
            | Rvalue::Aggregate(..)
            | Rvalue::WrapUnsafeBinder(..) => {
                // No modification is possible through these r-values.
                RangeLattice::Top
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
            TerminatorKind::SwitchInt { .. }
            | TerminatorKind::TailCall { .. }
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
                // FIXME: check if that is true
            }
        }
        terminator.edges()
    }

    fn handle_call_return(
        &self,
        return_places: CallReturnPlaces<'_, 'tcx>,
        state: &mut State<RangeLattice>,
    ) {
        // FIXME: not interprocedural yet
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

        if ty.is_bool() {
            match constant.const_.try_eval_bool(self.tcx, self.typing_env) {
                Some(true) => RangeLattice::Range(Range::singleton(ScalarInt::TRUE, false)),
                Some(false) => RangeLattice::Range(Range::singleton(ScalarInt::FALSE, false)),
                None => RangeLattice::Range(Range::new(ScalarInt::FALSE, ScalarInt::TRUE, false)),
            }
        } else if ty.is_integral() {
            match constant.const_.try_eval_scalar_int(self.tcx, self.typing_env) {
                Some(scalar_int) => {
                    RangeLattice::Range(Range::singleton(scalar_int, ty.is_signed()))
                }
                None => {
                    if let Some(type_range) = self.get_type_range(ty) {
                        RangeLattice::Range(type_range)
                    } else {
                        RangeLattice::Top
                    }
                }
            }
        } else {
            RangeLattice::Top
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
                    Add | Sub | Mul | Div => self.arith_interval(op, l, r, size, signed),
                    BitAnd | BitOr | BitXor => self.bitwise_interval(op, l, r, size),
                    // FIXME: handle ShrUnchecked, ShlUnchecked
                    Shl | Shr => self.shift_interval(op, l, r, size, signed),
                    Eq | Ne | Lt | Le | Gt | Ge => self.bool_interval(op, l, r, size, signed),
                    _ => return (RangeLattice::Top, RangeLattice::Top),
                };

                (res, res)
            }
            (RangeLattice::Bottom, _)
            | (_, RangeLattice::Bottom)
            | (RangeLattice::Range(_), _)
            | (_, RangeLattice::Range(_))
            | (RangeLattice::Top, RangeLattice::Top) => {
                (RangeLattice::Bottom, RangeLattice::Bottom)
            }
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
        use BinOp::*;

        // Get the type and layout for creating ImmTy values
        let ty = if signed {
            match size.bytes() {
                1 => self.tcx.types.i8,
                2 => self.tcx.types.i16,
                4 => self.tcx.types.i32,
                8 => self.tcx.types.i64,
                16 => self.tcx.types.i128,
                _ => return RangeLattice::Top,
            }
        } else {
            match size.bytes() {
                1 => self.tcx.types.u8,
                2 => self.tcx.types.u16,
                4 => self.tcx.types.u32,
                8 => self.tcx.types.u64,
                16 => self.tcx.types.u128,
                _ => return RangeLattice::Top,
            }
        };
        let Ok(layout) = self.tcx.layout_of(self.typing_env.as_query_input(ty)) else {
            return RangeLattice::Top;
        };

        // Evaluate all corner cases using ecx
        let candidates = [(l.lo, r.lo), (l.lo, r.hi), (l.hi, r.lo), (l.hi, r.hi)];

        let mut results: Vec<ScalarInt> = Vec::new();
        let mut ecx = self.ecx.borrow_mut();

        for (left_val, right_val) in candidates.iter() {
            // Convert ScalarInt to Scalar
            let left_scalar = Scalar::from_uint(left_val.to_bits_unchecked(), size);
            let right_scalar = Scalar::from_uint(right_val.to_bits_unchecked(), size);

            // Create ImmTy values
            let left_imm = ImmTy::from_scalar(left_scalar, layout);
            let right_imm = ImmTy::from_scalar(right_scalar, layout);

            // Evaluate using ecx
            if let Some(result) = ecx.binary_op(op, &left_imm, &right_imm).discard_err() {
                let scalar = result.to_scalar();
                if let Ok(scalar_int) = scalar.try_to_scalar_int() {
                    results.push(scalar_int);
                }
            }
        }

        drop(ecx);

        if results.is_empty() {
            return RangeLattice::Top;
        }

        // Find min and max from results
        let min_val = results
            .iter()
            .min_by(|a, b| {
                if signed {
                    a.to_int(size).cmp(&b.to_int(size))
                } else {
                    a.to_uint(size).cmp(&b.to_uint(size))
                }
            })
            .unwrap();
        let max_val = results
            .iter()
            .max_by(|a, b| {
                if signed {
                    a.to_int(size).cmp(&b.to_int(size))
                } else {
                    a.to_uint(size).cmp(&b.to_uint(size))
                }
            })
            .unwrap();

        RangeLattice::Range(Range::new(*min_val, *max_val, signed))
    }

    fn bitwise_interval(&self, op: BinOp, l: Range, r: Range, size: Size) -> RangeLattice {
        use std::cmp::{max, min};

        use BinOp::*;

        let signed = l.signed;
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

                if !signed {
                    // 0 <= (a & b) <= min(a, b)
                    let l_hi = to_u(l.hi);
                    let r_hi = to_u(r.hi);
                    let hi = from_u(l_hi.min(r_hi));
                    let lo = from_u(0);
                    RangeLattice::Range(Range::new(lo, hi, signed))
                } else {
                    // FIXME: might be able to optimize
                    RangeLattice::Top
                }
            }

            BitOr => {
                if l.lo == l.hi && r.lo == r.hi {
                    let res = from_u(to_u(l.lo) | to_u(r.lo));
                    return RangeLattice::Range(Range::singleton(res, signed));
                }

                if !signed {
                    // min >= max(lo_l, lo_r)
                    // max <= hi_l | hi_r.
                    let l_lo = to_u(l.lo);
                    let r_lo = to_u(r.lo);
                    let l_hi = to_u(l.hi);
                    let r_hi = to_u(r.hi);

                    let lo = from_u(l_lo.max(r_lo));
                    let hi = from_u(l_hi | r_hi);

                    RangeLattice::Range(Range::new(lo, hi, signed))
                } else {
                    // FIXME: might be able to optimize
                    RangeLattice::Top
                }
            }

            BitXor => {
                if l.lo == l.hi && r.lo == r.hi {
                    let res = from_u(to_u(l.lo) ^ to_u(r.lo));
                    return RangeLattice::Range(Range::singleton(res, signed));
                }

                if !signed {
                    let mask = size.truncate(u128::MAX);
                    let lo = from_u(0);
                    let hi = from_u(mask);
                    RangeLattice::Range(Range::new(lo, hi, signed))
                } else {
                    // FIXME: might be able to optimize
                    RangeLattice::Top
                }
            }
            _ => unreachable!(),
        }
    }

    fn shift_interval(
        &self,
        op: BinOp,
        l: Range,
        r: Range,
        size: Size,
        signed: bool,
    ) -> RangeLattice {
        use BinOp::*;

        // Get the type and layout for creating ImmTy values
        let ty = if signed {
            match size.bytes() {
                1 => self.tcx.types.i8,
                2 => self.tcx.types.i16,
                4 => self.tcx.types.i32,
                8 => self.tcx.types.i64,
                16 => self.tcx.types.i128,
                _ => return RangeLattice::Top,
            }
        } else {
            match size.bytes() {
                1 => self.tcx.types.u8,
                2 => self.tcx.types.u16,
                4 => self.tcx.types.u32,
                8 => self.tcx.types.u64,
                16 => self.tcx.types.u128,
                _ => return RangeLattice::Top,
            }
        };
        let Ok(layout) = self.tcx.layout_of(self.typing_env.as_query_input(ty)) else {
            return RangeLattice::Top;
        };

        // For shift operations, we need to evaluate all combinations of l.{lo,hi} with r.{lo,hi}
        let candidates = [(l.lo, r.lo), (l.lo, r.hi), (l.hi, r.lo), (l.hi, r.hi)];

        let mut results: Vec<ScalarInt> = Vec::new();
        let mut ecx = self.ecx.borrow_mut();

        for (left_val, right_val) in candidates.iter() {
            // Convert ScalarInt to Scalar
            let left_scalar = Scalar::from_uint(left_val.to_bits_unchecked(), size);
            let right_scalar = Scalar::from_uint(right_val.to_bits_unchecked(), size);

            // Create ImmTy values
            let left_imm = ImmTy::from_scalar(left_scalar, layout);
            let right_imm = ImmTy::from_scalar(right_scalar, layout);

            // Evaluate using ecx
            if let Some(result) = ecx.binary_op(op, &left_imm, &right_imm).discard_err() {
                let scalar = result.to_scalar();
                if let Ok(scalar_int) = scalar.try_to_scalar_int() {
                    results.push(scalar_int);
                }
            }
        }

        drop(ecx);

        if results.is_empty() {
            return RangeLattice::Top;
        }

        // Find min and max from results
        let min_val = results
            .iter()
            .min_by(|a, b| {
                if signed {
                    a.to_int(size).cmp(&b.to_int(size))
                } else {
                    a.to_uint(size).cmp(&b.to_uint(size))
                }
            })
            .unwrap();
        let max_val = results
            .iter()
            .max_by(|a, b| {
                if signed {
                    a.to_int(size).cmp(&b.to_int(size))
                } else {
                    a.to_uint(size).cmp(&b.to_uint(size))
                }
            })
            .unwrap();

        RangeLattice::Range(Range::new(*min_val, *max_val, signed))
    }

    fn bool_interval(
        &self,
        op: BinOp,
        l: Range,
        r: Range,
        size: Size,
        signed: bool,
    ) -> RangeLattice {
        use BinOp::*;

        let make_bool_range =
            |always_true: bool, always_false: bool, _this: &IntegerRangeAnalysis<'_, '_>| {
                let signed = false;
                if always_true && !always_false {
                    RangeLattice::Range(Range::singleton(ScalarInt::TRUE, signed))
                } else if always_false && !always_true {
                    RangeLattice::Range(Range::singleton(ScalarInt::FALSE, signed))
                } else {
                    RangeLattice::Range(Range::new(ScalarInt::FALSE, ScalarInt::TRUE, signed))
                }
            };

        // FIXME: more elegant way to handle signedness?
        let (always_true, always_false) = if signed {
            let to_i = |s: ScalarInt| -> i128 { s.to_int(size) };
            let ll = to_i(l.lo);
            let lh = to_i(l.hi);
            let rl = to_i(r.lo);
            let rh = to_i(r.hi);

            match op {
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
                _ => unreachable!(),
            }
        } else {
            let to_u = |s: ScalarInt| -> u128 { s.to_uint(size) };
            let ll = to_u(l.lo);
            let lh = to_u(l.hi);
            let rl = to_u(r.lo);
            let rh = to_u(r.hi);

            match op {
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
                _ => unreachable!(),
            }
        };

        make_bool_range(always_true, always_false, self)
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
        // FIXME:
    }

    fn eval_operand(&self, op: &Operand<'tcx>, state: &mut State<RangeLattice>) -> RangeLattice {
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
        // FIXME:
    }

    fn eval_discriminant(&self, enum_ty: Ty<'tcx>, variant_index: VariantIdx) -> Option<Scalar> {
        // FIXME:
        None
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
    fn visit_after_primary_statement_effect(
        &mut self,
        _analysis: &IntegerRangeAnalysis<'a, 'tcx>,
        state: &State<RangeLattice>,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        // Check for assignments that can be constant-propagated
        // FIXME: handle unary operations
        if let StatementKind::Assign(box (place, rvalue)) = &statement.kind {
            if let Rvalue::BinaryOp(op, box (left, right)) = rvalue {
                let mut state_mut = state.clone();
                // FIXME: handle overflows
                let (result, _) = self.analysis.binary_op(&mut state_mut, *op, left, right);

                // Can only constant-propagate if the range is a singleton
                let RangeLattice::Range(range) = result else {
                    return;
                };
                if range.lo != range.hi {
                    return;
                }

                // Can only constant-propagate bools and integers
                let ty = place.ty(self.body.local_decls(), self.tcx).ty;
                let const_val = {
                    if ty.is_bool() {
                        match range.lo {
                            ScalarInt::TRUE => Const::from_bool(self.tcx, true),
                            ScalarInt::FALSE => Const::from_bool(self.tcx, false),
                            _ => bug!(
                                "Expected ScalarInt::TRUE or ScalarInt::FALSE, got {:#?}",
                                range.lo
                            ),
                        }
                    } else if ty.is_integral() {
                        Const::from_scalar(self.tcx, Scalar::Int(range.lo), ty)
                    } else {
                        return;
                    }
                };

                let const_operand = Operand::Constant(Box::new(ConstOperand {
                    span: statement.source_info.span,
                    const_: const_val,
                    user_ty: None,
                }));

                // Replace the statement: nop the old one and add the new one
                self.patch.nop_statement(location);
                self.patch.add_assign(location, *place, Rvalue::Use(const_operand));
            }
        }
    }

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
                /* FIXME: if there are multiple targets, we don't eliminate the otherwise branch
                    even if it is not possible to take the otherwise branch.

                    e.g. only the 2 branch below is removed

                    fn test(x: bool) -> &'static str {
                        match x as u8 {
                            0 => "null",
                            1 => "one",
                            2 => "two",     // Unreachable
                            _ => "unknown", // Unreachable
                        }
                    }
                */

                let mut state_mut = state.clone();
                let value = self.analysis.eval_operand(discr, &mut state_mut);

                if let RangeLattice::Range(Range { lo, hi, .. }) = value {
                    // Check if the discriminant is a singleton
                    if lo == hi {
                        let bits = lo.to_bits_unchecked();
                        let target = targets.target_for_value(bits);
                        self.patch
                            .patch_terminator(location.block, TerminatorKind::Goto { target });
                        return;
                    }

                    // Filter out unreachable targets based on range
                    let lo_bits = lo.to_bits_unchecked();
                    let hi_bits = hi.to_bits_unchecked();

                    let filtered: Vec<_> = targets
                        .iter()
                        .filter(|(value, _)| *value >= lo_bits && *value <= hi_bits)
                        .collect();

                    let num_filtered_targets = filtered.len();

                    // If only the otherwise target remains, replace with goto
                    if num_filtered_targets == 0 {
                        let otherwise = targets.otherwise();
                        self.patch.patch_terminator(
                            location.block,
                            TerminatorKind::Goto { target: otherwise },
                        );
                    } else if num_filtered_targets < targets.iter().count() {
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
                } else if matches!(value, RangeLattice::Bottom) {
                    // FIXME: handle unreachable targets
                    //dbg!(&discr);
                    // self.patch.patch_terminator(location.block, TerminatorKind::Unreachable);
                }
            }
            _ => {}
        }
    }
}
