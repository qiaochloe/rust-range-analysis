//@ test-mir-pass: RangeAnalysisPass

// EMIT_MIR path_sensitivity.test.RangeAnalysisPass.diff
fn test(x: u8, y: bool, z: bool) {
    // CHECK-LABEL: fn test(
    if x < 5 {
        assert!(x < 5);
    }

    if !y {
        assert!(y as u8 == 0);
    }

    let w = z;
    if !w {
        assert!(z as u8 == 0);
        assert!(w as u8 == 0);
    }

    match x {
        1 => assert!(x == 1),
        2 => assert!(x == 2),
        10 => assert!(x == 10),
        _ => (),
    }

    match x + 1 {
        1 => assert!(x == 0),
        2 => assert!(x == 1),
        10 => assert!(x == 9),
        _ => (),
    }
}
