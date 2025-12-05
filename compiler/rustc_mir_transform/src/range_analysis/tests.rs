use crate::integer_range::*;
use std::num::NonZero;
use rustc_abi::Size;

// FIXME: test bool interval and shift interval
fn make_scalar_int(value: u128, size_bytes: u8) -> ScalarInt {
    let size = Size::from_bytes(size_bytes);
    ScalarInt::try_from_uint(value, size).unwrap()
}

fn make_signed_scalar_int(value: i128, size_bytes: u8) -> ScalarInt {
    let size = Size::from_bytes(size_bytes);
    ScalarInt::try_from_int(value, size).unwrap()
}

#[test]
fn test_range_singleton() {
    let val = make_scalar_int(5, 4);
    let range = Range::singleton(val, false);
    assert_eq!(range.lo, val);
    assert_eq!(range.hi, val);
    assert!(!range.signed);
}

#[test]
fn test_range_new() {
    let lo = make_scalar_int(1, 4);
    let hi = make_scalar_int(10, 4);
    let range = Range::new(lo, hi, false);
    assert_eq!(range.lo, lo);
    assert_eq!(range.hi, hi);
    assert!(!range.signed);
}

#[test]
fn test_range_join_unsigned() {
    let r1 = Range::new(make_scalar_int(1, 4), make_scalar_int(5, 4), false);
    let r2 = Range::new(make_scalar_int(3, 4), make_scalar_int(10, 4), false);
    let joined = r1.join(&r2);
    assert_eq!(joined.lo, make_scalar_int(1, 4));
    assert_eq!(joined.hi, make_scalar_int(10, 4));
    assert!(!joined.signed);
}

#[test]
fn test_range_join_signed() {
    // [-10, -5] join [-3, 5] should be [-10, 5]
    let r1_lo = make_signed_scalar_int(-10, 4);
    let r1_hi = make_signed_scalar_int(-5, 4);
    let r1 = Range::new(r1_lo, r1_hi, true);

    let r2_lo = make_signed_scalar_int(-3, 4);
    let r2_hi = make_signed_scalar_int(5, 4);
    let r2 = Range::new(r2_lo, r2_hi, true);

    let joined = r1.join(&r2);
    assert_eq!(joined.lo.to_int(Size::from_bytes(4)), -10);
    assert_eq!(joined.hi.to_int(Size::from_bytes(4)), 5);
    assert!(joined.signed);
}

#[test]
fn test_range_join_signed_negative() {
    // [-5, -1] join [-10, -3] should be [-10, -1]
    let r1 = Range::new(make_signed_scalar_int(-5, 4), make_signed_scalar_int(-1, 4), true);
    let r2 = Range::new(make_signed_scalar_int(-10, 4), make_signed_scalar_int(-3, 4), true);
    let joined = r1.join(&r2);
    assert_eq!(joined.lo.to_int(Size::from_bytes(4)), -10);
    assert_eq!(joined.hi.to_int(Size::from_bytes(4)), -1);
}

#[test]
fn test_range_intersect_unsigned() {
    let r1 = Range::new(make_scalar_int(1, 4), make_scalar_int(5, 4), false);
    let r2 = Range::new(make_scalar_int(3, 4), make_scalar_int(10, 4), false);
    let intersected = r1.intersect(r2).unwrap();
    assert_eq!(intersected.lo, make_scalar_int(3, 4));
    assert_eq!(intersected.hi, make_scalar_int(5, 4));
}

#[test]
fn test_range_intersect_disjoint() {
    let r1 = Range::new(make_scalar_int(1, 4), make_scalar_int(5, 4), false);
    let r2 = Range::new(make_scalar_int(10, 4), make_scalar_int(20, 4), false);
    assert!(r1.intersect(r2).is_none());
}

#[test]
fn test_range_intersect_signed() {
    // [-10, -5] intersect [-7, -3] should be [-7, -5]
    let r1 = Range::new(make_signed_scalar_int(-10, 4), make_signed_scalar_int(-5, 4), true);
    let r2 = Range::new(make_signed_scalar_int(-7, 4), make_signed_scalar_int(-3, 4), true);
    let intersected = r1.intersect(r2).unwrap();
    assert_eq!(intersected.lo.to_int(Size::from_bytes(4)), -7);
    assert_eq!(intersected.hi.to_int(Size::from_bytes(4)), -5);
}

#[test]
fn test_range_intersect_signed_negative_positive() {
    // [-5, 5] intersect [0, 10] should be [0, 5]
    let r1 = Range::new(make_signed_scalar_int(-5, 4), make_signed_scalar_int(5, 4), true);
    let r2 = Range::new(make_signed_scalar_int(0, 4), make_signed_scalar_int(10, 4), true);
    let intersected = r1.intersect(r2).unwrap();
    assert_eq!(intersected.lo.to_int(Size::from_bytes(4)), 0);
    assert_eq!(intersected.hi.to_int(Size::from_bytes(4)), 5);
}

#[test]
fn test_range_lattice_join() {
    let mut r1 =
        RangeLattice::Range(Range::new(make_scalar_int(1, 4), make_scalar_int(5, 4), false));
    let r2 =
        RangeLattice::Range(Range::new(make_scalar_int(3, 4), make_scalar_int(10, 4), false));
    let changed = r1.join(&r2);
    assert!(changed);
    match r1 {
        RangeLattice::Range(r) => {
            assert_eq!(r.lo, make_scalar_int(1, 4));
            assert_eq!(r.hi, make_scalar_int(10, 4));
        }
        _ => panic!("Expected Range"),
    }
}

#[test]
fn test_range_lattice_join_bottom() {
    let mut r1 = RangeLattice::Bottom;
    let r2 =
        RangeLattice::Range(Range::new(make_scalar_int(1, 4), make_scalar_int(5, 4), false));
    let changed = r1.join(&r2);
    assert!(changed);
    assert!(matches!(r1, RangeLattice::Range(_)));
}

#[test]
fn test_range_lattice_join_top() {
    let mut r1 = RangeLattice::Top;
    let r2 =
        RangeLattice::Range(Range::new(make_scalar_int(1, 4), make_scalar_int(5, 4), false));
    let changed = r1.join(&r2);
    assert!(!changed); // Top join anything = Top (no change)
    assert!(matches!(r1, RangeLattice::Top));
}

#[test]
fn test_range_lattice_join_identical() {
    let range = Range::new(make_scalar_int(1, 4), make_scalar_int(5, 4), false);
    let mut r1 = RangeLattice::Range(range);
    let r2 = RangeLattice::Range(range);
    let changed = r1.join(&r2);
    assert!(!changed); // Joining identical ranges shouldn't change
}

#[test]
fn test_range_compare_unsigned() {
    let range = Range::new(make_scalar_int(1, 4), make_scalar_int(10, 4), false);
    let a = make_scalar_int(5, 4);
    let b = make_scalar_int(3, 4);
    assert!(range.compare(a, b).is_gt());
}

#[test]
fn test_range_compare_signed_negative() {
    // Test that -5 < -3 for signed integers
    let range = Range::new(make_signed_scalar_int(-10, 4), make_signed_scalar_int(10, 4), true);
    let a = make_signed_scalar_int(-5, 4);
    let b = make_signed_scalar_int(-3, 4);
    assert!(range.compare(a, b).is_lt());
}

#[test]
fn test_range_compare_signed_vs_unsigned() {
    // Test that signed comparison differs from unsigned for negative numbers
    // In unsigned: 0xFFFFFFFB (u32 representation of -5) > 0xFFFFFFFD (u32 representation of -3)
    // In signed: -5 < -3
    let signed_range =
        Range::new(make_signed_scalar_int(-10, 4), make_signed_scalar_int(10, 4), true);
    let unsigned_range =
        Range::new(make_scalar_int(0xFFFFFFFB, 4), make_scalar_int(0xFFFFFFFD, 4), false);

    let a = make_signed_scalar_int(-5, 4);
    let b = make_signed_scalar_int(-3, 4);

    // Signed comparison: -5 < -3
    assert!(signed_range.compare(a, b).is_lt());
    let a_unsigned = make_scalar_int(0xFFFFFFFB, 4); // -5 as u32
    let b_unsigned = make_scalar_int(0xFFFFFFFD, 4); // -3 as u32
    // As unsigned, 0xFF...FB < 0xFF...FD
    assert!(unsigned_range.compare(a_unsigned, b_unsigned).is_lt());
}

#[test]
fn test_range_large_values() {
    // Test that ranges work correctly for large values that would overflow u8
    let large_val = make_scalar_int(1000, 4);
    let range = Range::singleton(large_val, false);
    assert_eq!(range.lo, large_val);
    assert_eq!(range.hi, large_val);
}

#[test]
fn test_range_different_sizes() {
    let u8_val = make_scalar_int(255, 1);
    let u16_val = make_scalar_int(1000, 2);
    let u32_val = make_scalar_int(100000, 4);

    let r1 = Range::singleton(u8_val, false);
    let r2 = Range::singleton(u16_val, false);
    let r3 = Range::singleton(u32_val, false);

    assert_eq!(r1.lo.size().bytes(), 1);
    assert_eq!(r2.lo.size().bytes(), 2);
    assert_eq!(r3.lo.size().bytes(), 4);
}

#[test]
fn test_range_join_preserves_signedness() {
    let r1 = Range::new(make_scalar_int(1, 4), make_scalar_int(5, 4), true);
    let r2 = Range::new(make_scalar_int(3, 4), make_scalar_int(10, 4), true);
    let joined = r1.join(&r2);
    assert!(joined.signed);
}

#[test]
#[should_panic]
fn test_range_join_different_signedness_panics() {
    let r1 = Range::new(make_scalar_int(1, 4), make_scalar_int(5, 4), false);
    let r2 = Range::new(make_scalar_int(3, 4), make_scalar_int(10, 4), true);
    let _joined = r1.join(&r2); // Should panic with bug!()
}

#[test]
#[should_panic]
fn test_range_intersect_different_signedness_panics() {
    let r1 = Range::new(make_scalar_int(1, 4), make_scalar_int(5, 4), false);
    let r2 = Range::new(make_scalar_int(3, 4), make_scalar_int(10, 4), true);
    let _intersected = r1.intersect(r2); // Should panic with bug!()
}

#[test]
fn test_range_intersect_touching() {
    // [1, 5] intersect [5, 10] should be [5, 5] (singleton)
    let r1 = Range::new(make_scalar_int(1, 4), make_scalar_int(5, 4), false);
    let r2 = Range::new(make_scalar_int(5, 4), make_scalar_int(10, 4), false);
    let intersected = r1.intersect(r2).unwrap();
    assert_eq!(intersected.lo, intersected.hi);
    assert_eq!(intersected.lo, make_scalar_int(5, 4));
}

#[test]
fn test_range_join_overlapping() {
    // [1, 10] join [5, 15] should be [1, 15]
    let r1 = Range::new(make_scalar_int(1, 4), make_scalar_int(10, 4), false);
    let r2 = Range::new(make_scalar_int(5, 4), make_scalar_int(15, 4), false);
    let joined = r1.join(&r2);
    assert_eq!(joined.lo, make_scalar_int(1, 4));
    assert_eq!(joined.hi, make_scalar_int(15, 4));
}

#[test]
fn test_range_join_adjacent() {
    // [1, 5] join [6, 10] should be [1, 10]
    let r1 = Range::new(make_scalar_int(1, 4), make_scalar_int(5, 4), false);
    let r2 = Range::new(make_scalar_int(6, 4), make_scalar_int(10, 4), false);
    let joined = r1.join(&r2);
    assert_eq!(joined.lo, make_scalar_int(1, 4));
    assert_eq!(joined.hi, make_scalar_int(10, 4));
}

#[test]
fn test_range_intersect_singleton() {
    // [5, 5] intersect [3, 7] should be [5, 5]
    let r1 = Range::singleton(make_scalar_int(5, 4), false);
    let r2 = Range::new(make_scalar_int(3, 4), make_scalar_int(7, 4), false);
    let intersected = r1.intersect(r2).unwrap();
    assert_eq!(intersected.lo, intersected.hi);
    assert_eq!(intersected.lo, make_scalar_int(5, 4));
}

#[test]
fn test_range_intersect_singleton_outside() {
    // [5, 5] intersect [10, 20] should be None
    let r1 = Range::singleton(make_scalar_int(5, 4), false);
    let r2 = Range::new(make_scalar_int(10, 4), make_scalar_int(20, 4), false);
    assert!(r1.intersect(r2).is_none());
}
}
