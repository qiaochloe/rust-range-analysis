//@ test-mir-pass: IntegerRange

// EMIT_MIR comparison_ops.test.IntegerRange.diff
fn test(x: u8, y: u8) -> bool {
    // CHECK-LABEL: fn test(
    // CHECK: const true
    let lt_result = if x <= 10 && y >= 20 {
        x < y // always true
    } else {
        false
    };

    // CHECK: const false
    let gt_result = if x <= 10 && y >= 20 {
        x > y // Always false
    } else {
        true
    };

    // CHECK: const true
    let eq_result = if x == 5 {
        x == 5 // Always true
    } else {
        false
    };

    // CHECK: const true
    let ne_result = if x <= 10 && y >= 20 {
        x != y // Always true
    } else {
        false
    };

    lt_result && !gt_result && eq_result && ne_result
}
