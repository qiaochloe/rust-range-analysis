//@ test-mir-pass: IntegerRange

// EMIT_MIR constant_prop.test.IntegerRange.diff
fn test() -> u8 {
    // CHECK-LABEL: fn test(
    // CHECK: const 15_u8
    // Test constant addition: 5 + 10 = 15
    let x = 5u8;
    let y = 10u8;
    let sum = x + y;

    // CHECK: const 50_u8
    // Test constant multiplication: 5 * 10 = 50
    let prod = x * y;

    // CHECK: const 4_u8
    // Test constant bitwise AND: 5 & 12 = 4
    let z = 12u8;
    let bitwise = x & z;
    sum + prod + bitwise
}
