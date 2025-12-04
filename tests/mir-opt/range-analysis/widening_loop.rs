//@ test-mir-pass: IntegerRange

// EMIT_MIR widening_loop.test.IntegerRange.diff
fn test() -> u8 {
    0
    //// CHECK-LABEL: fn test(
    //let mut i = 0u8;
    //// This loop would cause infinite growth without widening.
    //// With jump-set widening, when i grows from [0, n] to [0, n+1],
    //// widening should jump to the next threshold in the jump-set.
    //// For u8, jump-set is [0, 1, 255], so after growth it should widen to [0, 255].
    //loop {
    //    if i >= 1 {
    //        break;
    //    }
    //    i += 1;
    //    // At this point, i should be widened to [0, 255] due to jump-set widening
    //}
    //i
}
