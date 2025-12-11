//@ test-mir-pass: RangeAnalysisPass

// EMIT_MIR nested_loop.test.RangeAnalysisPass.diff
fn test() -> bool {
    // CHECK-LABEL: fn test(
    let mut cond = true;
    let mut k = 0;
    while k < 100 {
        cond = k >= 0;
        cond = k <= 99;
        let mut i = 0;
        let mut j = k;
        while i < j {
            i += 1;
            j -= 1;
        }
        k += 1;
        cond = i >= 0;
        cond = j >= 0;
        cond = i <= 99;
        cond = j <= 99;
    }
    cond = k >= 100;
    return cond;
}
