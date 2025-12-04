//@ test-mir-pass: IntegerRange

// EMIT_MIR control_flow.test.IntegerRange.diff
fn test(x: u8, y: u8) {
    // CHECK-LABEL: fn test(
    if x <= 10 {
        // Always true, should be optimized to goto
        assert!(x <= 10);
    } else {
        // May be true or false, should remain as assert
        assert!(x < 100);
    }

    let and_result = x & y;
    let or_result = x | y;
    let xor_result = x ^ y;

    if x <= 10 && y <= 10 {
        assert!(and_result >= 0 && and_result <= 10);
        assert!(or_result >= 0 && or_result <= 10);
        assert!(xor_result >= 0 && xor_result <= 10);
    }
}
