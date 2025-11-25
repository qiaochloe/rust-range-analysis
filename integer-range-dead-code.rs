fn main(x: bool) -> &'static str {
    match x as u8 {
        0 => "null",
        1 => "one",
        2 => "two",     // Unreachable
        _ => "unknown", // Unreachable
    }
}

fn foo(x: u8) {
    let b = x / 2;
    assert!(b < 128);   // True
}

fn bar() {
    let k = 0;
    while k < 100 {
        let i = 0;
        let j = k;
        while i < j {
            i += 1;
            j -= 1;
        }
        k += 1

        assert!(k >= 0);
        assert!(k < 100);
        assert!(i >= 0);
        assert!(j >= 0);
        assert!(i <= 99);
        assert!(j <= 99);
    }
}
