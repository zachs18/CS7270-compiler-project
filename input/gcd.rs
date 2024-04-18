// uses Euclid's algorithm
fn gcd(a: usize, b: usize) -> usize {
    if b == 0 {
        return a;
    }
    gcd(a % b, b)
}

fn extended_euclid(a: usize, b: usize) -> (usize, usize, usize) {
    if a == 0 {
        return (b, 0, 1);
    }

    let (gcd, x1, y1) = extended_euclid(b % a, a);

    let x = y1 - (b / a) * x1;
    let y = x1;

    (gcd, x, y)
}
