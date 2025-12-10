//@ test-mir-pass: RangeAnalysisPass

// EMIT_MIR path_sensitivity.test.RangeAnalysisPass.diff
fn test(x: u8, y: u8) {
    // CHECK-LABEL: fn test(
    if x < 5 {
        assert!(x < 5);
    }
}
