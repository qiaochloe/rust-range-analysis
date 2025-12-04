//@ test-mir-pass: IntegerRange

// EMIT_MIR range_intersection.test.IntegerRange.diff
fn test(x: u8) {
    // CHECK-LABEL: fn test(
    // Test range intersection: x is [0, 255]
    // After x >= 10: x is [10, 255]
    // After x <= 20: x is [10, 20] (intersection)
    if x >= 10 {
        if x <= 20 {
            assert!(x >= 10 && x <= 20);
        } else {
            assert!(x > 20);
        }
    } else {
        assert!(x < 10);
    };
}
