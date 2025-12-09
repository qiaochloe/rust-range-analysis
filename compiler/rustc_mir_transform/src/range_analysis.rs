//! Range analysis finds lower and upper bounds to the values that variables can assume.

// FIXME:
// char to int conversions
// handle isize and usize
// path-sensitivity e.g. if x < 10 { assert!(x < 10) };

/* TESTS
NOT OPTIMIZING:
comparison_ops
control_flow
range_intersection
switch_int_opt

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
// FIXME: remove the allow list
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

use rustc_abi::{BackendRepr, FIRST_VARIANT, FieldIdx, Size, TyAndLayout, VariantIdx};
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

    fn to_masks(&self) -> Option<(u128, u128)> {
        if self.signed {
            return None;
        }
        let size = self.lo.size();
        let diff = self.lo.to_uint(size) ^ self.hi.to_uint(size);
        let leading = !0 << (128 - diff.leading_zeros());
        let zero_mask = !self.lo.to_uint(size) & leading;
        let one_mask = self.lo.to_uint(size) & leading;
        Some((zero_mask, one_mask))
    }

    pub fn is_singleton(&self) -> bool {
        self.lo == self.hi
    }

    pub fn is_equal(&self, other: &Range) -> bool {
        self.is_singleton() && other.is_singleton() && self.lo == other.lo
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RangeRelation {
    LeftLt,
    LeftLe,
    Overlap,
    LeftGe,
    LeftGt,
}

impl RangeRelation {
    fn from_ranges(l: &Range, r: &Range) -> Self {
        let cmp = if l.signed {
            l.hi.to_int(l.hi.size()).cmp(&r.lo.to_int(r.lo.size()))
        } else {
            l.hi.to_uint(l.hi.size()).cmp(&r.lo.to_uint(r.lo.size()))
        };
        if cmp.is_lt() {
            return RangeRelation::LeftLt;
        }
        if cmp.is_eq() {
            return RangeRelation::LeftLe;
        }
        let cmp = if l.signed {
            l.lo.to_int(l.lo.size()).cmp(&r.hi.to_int(r.hi.size()))
        } else {
            l.lo.to_uint(l.lo.size()).cmp(&r.hi.to_uint(r.hi.size()))
        };
        if cmp.is_gt() {
            return RangeRelation::LeftGt;
        }
        if cmp.is_eq() {
            return RangeRelation::LeftGe;
        }
        RangeRelation::Overlap
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RangeLattice {
    Bottom,
    Range(Range, u8),
    Top,
}

impl RangeLattice {
    fn range(range: Range) -> Self {
        RangeLattice::Range(range, 0)
    }
}

const JOIN_LIMIT: u8 = 10;

impl JoinSemiLattice for RangeLattice {
    fn join(&mut self, other: &Self) -> bool {
        match (&*self, other) {
            (Self::Top, _) | (_, Self::Bottom) => false,
            (Self::Bottom, Self::Range(x, _)) => {
                *self = Self::range(x.clone());
                true
            }
            (Self::Bottom, Self::Top) => {
                *self = Self::Top;
                true
            }
            (Self::Range(a, joins), Self::Range(b, _)) if *joins < JOIN_LIMIT => {
                let old = a.clone();
                let new = a.join(b);
                *self = Self::Range(new, *joins + 1);
                old != new
            }
            (Self::Range(..), _) => {
                *self = Self::Top;
                true
            }
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

const RANGE_TRUE: RangeLattice =
    RangeLattice::Range(Range { lo: ScalarInt::TRUE, hi: ScalarInt::TRUE, signed: false }, 0);
const RANGE_FALSE: RangeLattice =
    RangeLattice::Range(Range { lo: ScalarInt::FALSE, hi: ScalarInt::FALSE, signed: false }, 0);
const RANGE_BOOL: RangeLattice =
    RangeLattice::Range(Range { lo: ScalarInt::FALSE, hi: ScalarInt::TRUE, signed: false }, 0);

pub(super) struct RangeAnalysisPass;

impl<'tcx> crate::MirPass<'tcx> for RangeAnalysisPass {
    fn is_enabled(&self, sess: &rustc_session::Session) -> bool {
        sess.mir_opt_level() >= 3
    }

    /// Returns `true` if this pass can be overridden by `-Zenable-mir-passes`
    fn can_be_overridden(&self) -> bool {
        true
    }

    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        dbg!(&body.span);
        let place_limit = None;
        let map = Map::new(tcx, body, place_limit);

        let results = debug_span!("analyze")
            .in_scope(|| RangeAnalysis::new(tcx, body, map).iterate_to_fixpoint(tcx, body, None));

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
        // FIXME
        true
    }
}

struct RangeAnalysis<'a, 'tcx> {
    map: Map<'tcx>,
    tcx: TyCtxt<'tcx>,
    local_decls: &'a LocalDecls<'tcx>,
    ecx: RefCell<InterpCx<'tcx, DummyMachine>>,
    typing_env: ty::TypingEnv<'tcx>,
}

impl<'tcx> Analysis<'tcx> for RangeAnalysis<'_, 'tcx> {
    type Domain = State<RangeLattice>;

    const NAME: &'static str = "RangeAnalysis";

    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        State::Unreachable
    }

    fn initialize_start_block(&self, body: &Body<'tcx>, state: &mut Self::Domain) {
        assert_matches!(state, State::Unreachable);
        *state = State::new_reachable();
        for arg in body.args_iter() {
            let arg_ty = self.local_decls[arg].ty;
            let place_ref = PlaceRef { local: arg, projection: &[] };
            match self.get_type_range(arg_ty) {
                Some(type_range) => {
                    state.assign(
                        place_ref,
                        ValueOrPlace::Value(RangeLattice::range(type_range)),
                        &self.map,
                    );
                }
                None => {
                    state.flood(place_ref, &self.map);
                }
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

impl<'a, 'tcx> RangeAnalysis<'a, 'tcx> {
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
                // FIXME: check, taken from dataflow_const_prop.rs
                state.flood_discr(place.as_ref(), &self.map);
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
                    RangeLattice::Range(range, _) => {
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
                            RangeLattice::range(type_range)
                        } else {
                            let converted_range = Range::new(lo, hi, target_signed);
                            converted_range
                                .intersect(type_range)
                                .map(RangeLattice::range)
                                .unwrap_or(RangeLattice::Top)
                        }
                    }
                    RangeLattice::Bottom => RangeLattice::Bottom,
                    RangeLattice::Top => {
                        // If operand is Top, check if we can at least provide the target type's range
                        self.get_type_range(*ty)
                            .map(RangeLattice::range)
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
                self.get_type_range(*ty).map(RangeLattice::range).unwrap_or(RangeLattice::Top)
            }

            Rvalue::Cast(CastKind::FloatToFloat, _operand, _ty) => {
                // Float ranges are not tracked
                RangeLattice::Top
            }

            Rvalue::Cast(CastKind::Transmute | CastKind::Subtype, operand, ty) => {
                // Transmute and subtype casts are not handled
                RangeLattice::Top
            }

            Rvalue::BinaryOp(op, box (left, right)) if !op.is_overflowing() => {
                // Overflows must be ignored here.
                // The overflowing operators are handled in `handle_assign`.
                let (val, _overflow) = self.binary_op(state, *op, left, right);
                val
            }

            Rvalue::UnaryOp(op, operand) => self.unary_op(state, *op, operand),

            Rvalue::NullaryOp(NullOp::RuntimeChecks(_)) => RangeLattice::Top,

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
            }
        }
        terminator.edges()
    }

    fn handle_call_return(
        &self,
        return_places: CallReturnPlaces<'_, 'tcx>,
        state: &mut State<RangeLattice>,
    ) {
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
                Some(true) => RANGE_TRUE,
                Some(false) => RANGE_FALSE,
                None => RANGE_BOOL,
            }
        } else if ty.is_integral() {
            match constant.const_.try_eval_scalar_int(self.tcx, self.typing_env) {
                Some(scalar_int) => {
                    RangeLattice::range(Range::singleton(scalar_int, ty.is_signed()))
                }
                None => {
                    self.get_type_range(ty).map(RangeLattice::range).unwrap_or(RangeLattice::Top)
                }
            }
        } else {
            RangeLattice::Top
        }
    }

    fn unary_op(
        &self,
        state: &mut State<RangeLattice>,
        op: UnOp,
        operand: &Operand<'tcx>,
    ) -> RangeLattice {
        let lat = self.eval_operand(operand, state);
        match lat {
            RangeLattice::Range(range, _) => {
                let ty = operand.ty(self.local_decls, self.tcx);
                if !ty.is_integral() && !ty.is_bool() {
                    return RangeLattice::Top;
                }
                let Ok(layout) = self.tcx.layout_of(self.typing_env.as_query_input(ty)) else {
                    return RangeLattice::Top;
                };
                self.unary_interval(op, range, layout)
            }
            RangeLattice::Bottom => RangeLattice::Bottom,
            RangeLattice::Top => RangeLattice::Top,
        }
    }

    fn unary_interval(
        &self,
        op: UnOp,
        range: Range,
        layout: TyAndLayout<'tcx, Ty<'tcx>>,
    ) -> RangeLattice {
        type RL = RangeLattice;
        let signed = range.signed;
        let mut ecx = self.ecx.borrow_mut();
        let type_range = self.get_type_range(layout.ty).map(RL::range).unwrap_or(RL::Top);

        // Performs a unary operation using ecx
        let eval = |operand: ScalarInt, op: UnOp| -> Option<ScalarInt> {
            let imm = ImmTy::from_scalar_int(operand, layout);
            ecx.unary_op(op, &imm)
                .discard_err()
                .and_then(|result| result.to_scalar().try_to_scalar_int().ok())
        };

        let to_range = |opt: Option<ScalarInt>| -> RL {
            opt.map(|val| RL::range(Range::singleton(val, signed))).unwrap_or(type_range)
        };

        use UnOp::*;
        match op {
            UnOp::Not | UnOp::Neg => {
                if range.is_singleton() {
                    to_range(eval(range.lo, op))
                } else {
                    type_range
                }
            }
            UnOp::PtrMetadata => unreachable!(),
        }
    }

    /// Must only be run without overflows
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
            (RangeLattice::Range(l, _), RangeLattice::Range(r, _)) => {
                let ty = left.ty(self.local_decls, self.tcx);
                if !ty.is_integral() && !ty.is_bool() {
                    return (RangeLattice::Top, RangeLattice::Top);
                }
                let Ok(layout) = self.tcx.layout_of(self.typing_env.as_query_input(ty)) else {
                    return (RangeLattice::Top, RangeLattice::Top);
                };
                self.binary_interval(op, l, r, layout)
            }
            (RangeLattice::Bottom, _)
            | (_, RangeLattice::Bottom)
            | (RangeLattice::Range(_, _), _)
            | (_, RangeLattice::Range(_, _))
            | (RangeLattice::Top, RangeLattice::Top) => {
                (RangeLattice::Bottom, RangeLattice::Bottom)
            }
        }
    }

    /// Returns (value_range, overflow_range)
    fn binary_interval(
        &self,
        op: BinOp,
        l: Range,
        r: Range,
        layout: TyAndLayout<'tcx, Ty<'tcx>>,
    ) -> (RangeLattice, RangeLattice) {
        type RL = RangeLattice;
        let size = layout.size;
        let signed = l.signed;

        let mut ecx = self.ecx.borrow_mut();
        let cmp = RangeRelation::from_ranges(&l, &r);
        let type_range = self.get_type_range(layout.ty).map(RL::range).unwrap_or(RL::Top);

        // Performs a binary operation using ecx
        let eval_ecx = |l: ScalarInt, r: ScalarInt, op: BinOp| -> Option<ImmTy<'_>> {
            let left_imm = ImmTy::from_scalar_int(l, layout);
            let right_imm = ImmTy::from_scalar_int(r, layout);
            ecx.binary_op(op, &left_imm, &right_imm).discard_err()
        };

        // Performs a non-overflowing binary operation
        let eval_base = |l: ScalarInt, r: ScalarInt, op: BinOp| -> Option<ScalarInt> {
            assert!(!op.is_overflowing());
            eval_ecx(l, r, op).and_then(|result| result.to_scalar().try_to_scalar_int().ok())
        };

        // Performs an overflowing binary operation
        let eval_over = |l: ScalarInt, r: ScalarInt, op: BinOp| -> (Option<ScalarInt>, bool) {
            assert!(op.is_overflowing());
            // FIXME: is unwrap okay?
            let (res, overflow) = eval_ecx(l, r, op).unwrap().to_scalar_pair();
            (res.try_to_scalar_int().ok(), overflow.to_bool().discard_err().unwrap())
        };

        let to_range = |opt: Option<ScalarInt>| -> RL {
            opt.map(|val| RL::range(Range::singleton(val, signed))).unwrap_or(type_range)
        };

        let to_range_pair = |min_opt: Option<ScalarInt>, max_opt: Option<ScalarInt>| -> RL {
            match (min_opt, max_opt) {
                (Some(min_val), Some(max_val)) => RL::range(Range::new(min_val, max_val, signed)),
                _ => type_range,
            }
        };

        use BinOp::*;
        match op {
            Add | AddWithOverflow if !signed => {
                // (l.lo + r.lo, l.hi + r.hi)
                let (lo, lo_over) = eval_over(l.lo, r.lo, AddWithOverflow);
                let (hi, hi_over) = eval_over(l.hi, r.hi, AddWithOverflow);
                if lo_over {
                    (to_range_pair(lo, hi), RANGE_TRUE)
                } else if !hi_over {
                    (to_range_pair(lo, hi), RANGE_FALSE)
                } else {
                    (type_range, RANGE_BOOL)
                }
            }

            Add | AddWithOverflow if signed => {
                // (l.lo + r.lo, l.hi + r.hi)
                let (lo, lo_over) = eval_over(l.lo, r.lo, AddWithOverflow);
                let (hi, hi_over) = eval_over(l.hi, r.hi, AddWithOverflow);
                if lo_over && hi_over && lo.unwrap().to_int(size) <= hi.unwrap().to_int(size) {
                    (to_range_pair(lo, hi), RANGE_TRUE)
                } else if !lo_over && !hi_over {
                    (to_range_pair(lo, hi), RANGE_FALSE)
                } else {
                    (type_range, RANGE_BOOL)
                }
            }

            Sub | SubWithOverflow if !signed => {
                // (l.lo - r.hi, l.hi - r.lo)
                let lo = eval_base(l.lo, r.hi, Sub);
                let hi = eval_base(l.hi, r.lo, Sub);
                if matches!(cmp, RangeRelation::LeftGe) {
                    (to_range_pair(lo, hi), RANGE_FALSE)
                } else if matches!(cmp, RangeRelation::LeftLt) {
                    (to_range_pair(lo, hi), RANGE_TRUE)
                } else {
                    (type_range, RANGE_BOOL)
                }
            }

            Sub | SubWithOverflow if signed => {
                // (l.lo - r.hi, l.hi - r.lo)
                let (lo, lo_over) = eval_over(l.lo, r.hi, SubWithOverflow);
                let (hi, hi_over) = eval_over(l.hi, r.lo, SubWithOverflow);
                if lo_over && hi_over && lo.unwrap().to_int(size) <= hi.unwrap().to_int(size) {
                    (to_range_pair(lo, hi), RANGE_TRUE)
                } else if !lo_over && !hi_over {
                    (to_range_pair(lo, hi), RANGE_FALSE)
                } else {
                    (type_range, RANGE_BOOL)
                }
            }

            Mul | MulWithOverflow => {
                let candidates = [(l.lo, r.lo), (l.lo, r.hi), (l.hi, r.lo), (l.hi, r.hi)];
                let mut results = Vec::new();
                for (l_val, r_val) in candidates {
                    let (res, over) = eval_over(l_val, r_val, MulWithOverflow);
                    if over {
                        return (type_range, RANGE_BOOL);
                    }
                    results.push(res.unwrap());
                }
                if signed {
                    results.sort_by(|a, b| a.to_int(size).cmp(&b.to_int(size)));
                } else {
                    results.sort_by(|a, b| a.to_uint(size).cmp(&b.to_uint(size)));
                }
                (RL::range(Range::new(results[0], results[3], signed)), RANGE_FALSE)
            }

            Div => {
                if !signed && r.lo.to_uint(size) == 0 {
                    return (RL::Top, RL::Top);
                }
                if signed && r.lo.to_int(size) <= 0 && r.hi.to_int(size) >= 0 {
                    return (RL::Top, RL::Top);
                }
                // Check MIN / -1, note that r can no longer contain 0
                if signed && l.lo.to_int(size) == size.signed_int_min() && r.hi.to_int(size) == -1 {
                    return (RL::Top, RL::Top);
                }
                let candidates = [(l.lo, r.lo), (l.lo, r.hi), (l.hi, r.lo), (l.hi, r.hi)];
                let mut results: Vec<ScalarInt> = candidates
                    .iter()
                    .map(|(l_val, r_val)| eval_base(*l_val, *r_val, Div).unwrap())
                    .collect();
                if signed {
                    results.sort_by(|a, b| a.to_int(size).cmp(&b.to_int(size)));
                } else {
                    results.sort_by(|a, b| a.to_uint(size).cmp(&b.to_uint(size)));
                }
                (RL::range(Range::new(results[0], results[3], signed)), RL::Top)
            }

            BitAnd | BitOr | BitXor if l.lo == l.hi && r.lo == r.hi => {
                (to_range(eval_base(l.lo, r.lo, op)), RL::Top)
            }

            BitAnd if !signed => {
                let (l_zero, l_one) = l.to_masks().unwrap();
                let (r_zero, r_one) = r.to_masks().unwrap();
                let one = l_one & r_one;
                let zero = l_zero | r_zero;
                let lo = ScalarInt::try_from_uint(one, size).unwrap();
                let hi = ScalarInt::try_from_uint(one | !zero, size).unwrap();
                (RL::range(Range::new(lo, hi, signed)), RL::Top)
                // FIXME: might be able to do signed optimizations
            }

            BitOr if !signed => {
                let (l_zero, l_one) = l.to_masks().unwrap();
                let (r_zero, r_one) = r.to_masks().unwrap();
                let one = l_one | r_one;
                let zero = l_zero & r_zero;
                let lo = ScalarInt::try_from_uint(one, size).unwrap();
                let hi = ScalarInt::try_from_uint(one | !zero, size).unwrap();
                (RL::range(Range::new(lo, hi, signed)), RL::Top)
                // FIXME: might be able to do signed optimizations
            }

            BitXor if !signed => {
                let (l_zero, l_one) = l.to_masks().unwrap();
                let (r_zero, r_one) = r.to_masks().unwrap();
                let one = l_one & r_zero | l_zero & r_one;
                let zero = l_zero & r_zero | l_one & r_one;
                let lo = ScalarInt::try_from_uint(one, size).unwrap();
                let hi = ScalarInt::try_from_uint(one | !zero, size).unwrap();
                (RL::range(Range::new(lo, hi, signed)), RL::Top)
                // FIXME: might be able to do signed optimizations
            }

            Eq => {
                if matches!(cmp, RangeRelation::LeftLt | RangeRelation::LeftGt) {
                    return (RANGE_FALSE, RL::Top);
                }
                (RANGE_BOOL, RL::Top)
            }

            Ne => {
                if matches!(cmp, RangeRelation::LeftLt | RangeRelation::LeftGt) {
                    return (RANGE_TRUE, RL::Top);
                }
                (RANGE_BOOL, RL::Top)
            }

            Lt => {
                if matches!(cmp, RangeRelation::LeftLt) {
                    (RANGE_TRUE, RL::Top)
                } else if matches!(cmp, RangeRelation::LeftGe) {
                    (RANGE_FALSE, RL::Top)
                } else {
                    (RANGE_BOOL, RL::Top)
                }
            }

            Le => {
                if matches!(cmp, RangeRelation::LeftLe) {
                    (RANGE_TRUE, RL::Top)
                } else if matches!(cmp, RangeRelation::LeftGt) {
                    (RANGE_FALSE, RL::Top)
                } else {
                    (RANGE_BOOL, RL::Top)
                }
            }

            Gt => {
                if matches!(cmp, RangeRelation::LeftGt) {
                    (RANGE_TRUE, RL::Top)
                } else if matches!(cmp, RangeRelation::LeftLe) {
                    (RANGE_FALSE, RL::Top)
                } else {
                    (RANGE_BOOL, RL::Top)
                }
            }

            Ge => {
                if matches!(cmp, RangeRelation::LeftGe) {
                    (RANGE_TRUE, RL::Top)
                } else if matches!(cmp, RangeRelation::LeftLt) {
                    (RANGE_FALSE, RL::Top)
                } else {
                    (RANGE_BOOL, RL::Top)
                }
            }

            // FIXME: Shl, Shr
            _ => (type_range, RL::Top),
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

    fn eval_operand(&self, op: &Operand<'tcx>, state: &mut State<RangeLattice>) -> RangeLattice {
        let value = match self.handle_operand(op, state) {
            ValueOrPlace::Value(value) => value,
            ValueOrPlace::Place(place) => state.get_idx(place, &self.map),
        };
        value
    }
}

/// This is used to visualize the dataflow analysis.
impl<'tcx> DebugWithContext<RangeAnalysis<'_, 'tcx>> for State<RangeLattice> {
    fn fmt_with(&self, ctxt: &RangeAnalysis<'_, 'tcx>, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            State::Reachable(values) => debug_with_context(values, None, &ctxt.map, f),
            State::Unreachable => write!(f, "unreachable"),
        }
    }

    fn fmt_diff_with(
        &self,
        old: &Self,
        ctxt: &RangeAnalysis<'_, 'tcx>,
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
impl<'a, 'tcx> RangeAnalysis<'a, 'tcx> {
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
            RangeLattice::Range(Range { lo, hi, .. }, _) => {
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
    analysis: &'a RangeAnalysis<'a, 'tcx>,
    patch: MirPatch<'tcx>,
}

impl<'a, 'tcx> Collector<'a, 'tcx> {
    fn new(
        tcx: TyCtxt<'tcx>,
        body: &'a Body<'tcx>,
        results: &'a rustc_mir_dataflow::Results<'tcx, RangeAnalysis<'a, 'tcx>>,
    ) -> Self {
        Self { tcx, body, analysis: &results.analysis, patch: MirPatch::new(body) }
    }
}

impl<'a, 'tcx> ResultsVisitor<'tcx, RangeAnalysis<'a, 'tcx>> for Collector<'a, 'tcx> {
    fn visit_after_primary_statement_effect(
        &mut self,
        _analysis: &RangeAnalysis<'a, 'tcx>,
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
                let RangeLattice::Range(range, _) = result else {
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
        _analysis: &RangeAnalysis<'a, 'tcx>,
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

                if let RangeLattice::Range(Range { lo, hi, .. }, _) = value {
                    // Check if the range is a singleton
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
