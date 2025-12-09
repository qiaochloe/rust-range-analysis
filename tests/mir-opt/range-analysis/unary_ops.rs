//@ test-mir-pass: RangeAnalysisPass

// EMIT_MIR unary_ops.test.RangeAnalysisPass.diff
fn test(x: i8, y: i8, x_bool: bool, y_bool: bool) {
    // CHECK-LABEL: fn test(

    // Not
    let x_not = !x_bool as u8; // [0, 1] 
    let y_not = !y_bool as u8; // [0, 1]
    let z = x_not + y_not; // [0, 2]
    assert!(z >= 0 && z <= 2); // True

    let z = x_not + 1; // [0, 1] + [1, 1]
    assert!(z >= 1 && z <= 2); // True

    // Neg
    let x_neg = -x;
    let y_neg = -y;
    let z = x_neg + y_neg;
    assert!(z >= -128 && z <= 127);
}
