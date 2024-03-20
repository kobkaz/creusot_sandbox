use creusot_contracts::*;

#[ensures(
    forall <p : Int, q : Int, d : Int>
    d != 0 ==> 0 <= p ==> 0 <= q ==> p % d == 0 ==> q % d == 0 ==> (p + q) % d == 0)]
fn lemma_preserve_cd_add() {}

#[ensures(
    forall <p : Int, q : Int, d : Int>
    d != 0 ==> 0 <= q ==> q <= p ==> p % d == 0 ==> q % d == 0  ==> (p - q) % d == 0)]
fn lemma_preserve_cd_sub() {}

#[ensures(
    forall <p : Int, q : Int, d : Int>
    d != 0 ==> q % d == 0 ==> (p * q) % d == 0)]
fn lemma_divisor_mult() {}

#[logic]
fn is_common_divisor(a: Int, b: Int, d: Int) -> bool {
    a % d == 0 && b % d == 0 && d != 0
}

#[requires(a@ != 0 && b@ != 0)]
#[ensures(is_common_divisor(a@, b@, result@))]
#[ensures(forall<d:u64> is_common_divisor(a@, b@, d@) ==> result@ % d@ == 0)]
pub fn gcd(a: u64, b: u64) -> u64 {
    let (mut x, mut y) = if a < b { (a, b) } else { (b, a) };
    proof_assert!(x@ == (a@).min(b@));
    proof_assert!(y@ == (a@).max(b@));

    #[invariant(forall<d:Int> is_common_divisor(x@, y@, d) == is_common_divisor(a@, b@, d))]
    //#[invariant(cd, forall<d:Int> is_common_divisor(@a, @b, d) ==> is_common_divisor(@x, @y, d))]
    #[invariant(x@ <= y@)]
    #[invariant(y@ > 0)]
    while x != 0 {
        lemma_preserve_cd_add();
        lemma_preserve_cd_sub();
        lemma_divisor_mult();

        proof_assert!(y@ == (y@ / x@) * x@ + y@ % x@);
        proof_assert!(forall <d:Int> is_common_divisor(x@, y@ % x@, d) ==> y@ % d == 0);
        proof_assert!(y@ % x@  == y@ - (y@ / x@) * x@);
        proof_assert!(
            forall <d:Int> is_common_divisor(x@, y@, d) ==> (y@ - (y@ / x@) * x@) % d == 0);
        y = y % x;
        std::mem::swap(&mut x, &mut y);
    }

    proof_assert!(is_common_divisor(x@, y@, y@));
    y
}
