//@ test-mir-pass: IntegerRange

// EMIT_MIR int_to_int_cast.test.IntegerRange.diff
fn test(x: u8) -> u8 {
    // CHECK-LABEL: fn test(
    // Test u8 to u16 cast: x is [0, 255] (u8) -> [0, 255] (u16)
    let x_u16 = x as u16;
    assert!(x_u16 >= 0 && x_u16 <= 255);

    // Test u16 to u8 cast: x_u16 is [0, 255] (u16) -> [0, 255] (u8)
    let x_u8 = x_u16 as u8;
    assert!(x_u8 >= 0 && x_u8 <= 255);

    x_u8
}
