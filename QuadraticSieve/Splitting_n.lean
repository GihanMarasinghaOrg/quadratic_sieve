/- n|ab, n∤a, n∤b, then gcd(a,n) is a non-trivial factor of n.

prime factorisation stuff for the sake of the report.

if gcd(a,n)=n , then n|a, a contradiction.

if d=gcd(a,n)=1, then since n|ab and gcd(a,n)=1, gcd(a,n)=1=ax+ny for some integers x,y.
b=bax+bny, and n|bax since n|ba and n|bny since n|n. So n|b, a contradiction.

gcd(a,n)|n by definition of gcd.-/

import Mathlib


theorem non_trivial_factor : ∀ n a b : Nat, 0 < n → n ∣ a * b → ¬ n ∣ a → ¬ n ∣ b → n ≠ Nat.gcd a n ∧ 1 ≠ Nat.gcd a n := by
  intro n a b n_pos n_dvd_ab n_ndvd_a n_ndvd_b
  constructor
  · intro h
    have n_dvd_a : n ∣ a := by exact Nat.gcd_eq_right_iff_dvd.mp (id (Eq.symm h))
    contradiction
  by_contra h₁
  have h₂ := Nat.gcd_eq_gcd_ab a n
  rw[← h₁] at h₂
  have h₃ : ↑b = ↑b * ↑a * a.gcdA n + ↑b * ↑n * a.gcdB n := by
  /-   calc ↑b = ↑b * (1 : ℤ) := by ring
    _ = ↑b * (↑a * a.gcdA n + ↑n * a.gcdB n) := by rw[h₂]
    _ = ↑b * ↑a * a.gcdA n + ↑b * ↑n * a.gcdB n := by ring -/
    nth_rw 1 [← mul_one b]
    rw[Nat.cast_mul]
    rw[h₂]
    linarith
  /- have h₄ : ↑n ∣ ↑b * ↑a * a.gcdA n := by
    rw[mul_comm] at n_dvd_ab
    apply dvd_mul_of_dvd_left n_dvd_ab (a.gcdA n) -/
  have h₅ : (n : ℤ) ∣ (b : ℤ) := by
    rw[h₃]
    apply dvd_add
    · sorry
    rw[mul_comm ↑b (n : ℤ)]
    rw[mul_assoc]
    apply dvd_mul_right
  have h₄ : n ∣ b := by
    norm_cast at h₅
  contradiction
