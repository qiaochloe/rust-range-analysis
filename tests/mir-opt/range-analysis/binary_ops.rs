//@ test-mir-pass: IntegerRange

// EMIT_MIR binary_ops.test.IntegerRange.diff
fn test(x: u8, y: u8, x_signed: i8, y_signed: i8, shift: u8) {
    // CHECK-LABEL: fn test(
    // x is [0, 255], y is [0, 255]

    // Arithmetic ops
    let sum = x + y;
    let diff = x - y;
    let prod = x * y;
    let quot = if y != 0 { x / y } else { 0 };

    assert!(sum >= 0 && sum <= 255);
    assert!(prod >= 0 && prod <= 255);
    assert!(quot >= 0 && quot <= 255);
    assert!(diff >= 0 && diff <= 255);

    // Signed arithmetic
    let sum = x_signed + y_signed;
    let diff = x_signed - y_signed;
    let prod = x_signed * y_signed;

    assert!(sum >= -128 && sum <= 127);
    assert!(diff >= -128 && diff <= 127);
    assert!(prod >= -128 && prod <= 127);

    // Bitwise
    let and_result = x & y;
    let or_result = x | y;
    let xor_result = x ^ y;

    assert!(and_result >= 0 && and_result <= 255);
    assert!(or_result >= 0 && or_result <= 255);
    assert!(xor_result >= 0 && xor_result <= 255);

    // Shit ops
    let shl_result = x << shift;
    let shr_result = x >> shift;
    let shl_result2 = (y as u8) << shift;
    let shr_result2 = (y as u8) >> shift;

    assert!(shl_result >= 0 && shl_result <= 255);
    assert!(shr_result >= 0 && shr_result <= 255);
    assert!(shl_result2 >= 0 && shl_result2 <= 1);
    assert!(shr_result2 >= 0 && shr_result2 <= 1);
}
