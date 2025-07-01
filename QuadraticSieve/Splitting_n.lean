/- n|ab, n∤a, n∤b, then gcd(a,n) is a non-trivial factor of n.

prime factorisation stuff for the sake of the report.

if gcd(a,n)=n , then n|a, a contradiction.

if d=gcd(a,n)=1, then since n|ab and gcd(a,n)=1, gcd(a,n)=1=ax+ny for some integers x,y.
b=bax+bny, and n|bax since n|ba and n|bny since n|n. So n|b, a contradiction.

gcd(a,n)|n by definition of gcd.-/


theorem non_trivial_factor : ∀ n a b : Nat, 0 < n → n ∣ a * b → ¬ n ∣ a → ¬ n ∣ b → n ≠ Nat.gcd a n ∧ 1 ≠ Nat.gcd a n := by
  intro n a b n_pos n_dvd_ab n_ndvd_a n_ndvd_b
  constructor
  · intro h
    have n_dvd_a : n ∣ a := by exact Nat.gcd_eq_right_iff_dvd.mp (id (Eq.symm h))
    contradiction
  sorry
