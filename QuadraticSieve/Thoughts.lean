import Mathlib

/-
# Thoughts

Mid-goal: infer a² ≃ b² (mod n) given sufficiently many relations.

Smaller goals:

* Formalise the idea of a 'relation'. Either as a vector of as a function from
  a finite 'set' (the factor base) to F₂
* Formalise the idea of a factor base. Maybe a function for a fininte set to
  a set of primes plus a sign.


B = (-1, 2, 3, 5, 7, 11)

w = ( 1, 4, 3, 1, 5,  8)

v = ( 1, 0, 1, 1, 1,  0)

a = (-1)¹ ⬝ 2⁴ ⬝ 3³ ⬝ 5¹ ⬝ 7⁵ ⬝ 11⁸

We want to prove that a is a square if and only if v is the zero 'vector', given
that a factors over the factor base B.

More thoughts: we dont' want repetitions in B. That is, we can't have

B = (-1, 2, 2, 3)

So how best to represent B? Two possibilities
* Something like a set, but where we can talk about the i-th element of B or
* A function from a finite set, ι, to the set of integers with the the provisos
  that
  1. for each i ∈ ι, B i is -1 or a prime and
  2. B is injective.

## Next steps

* Formalise what it means for a to factor over B.
* Write a function that returns the vector w (the exponent vectors)
  for each a.
* Write a function that returns the vector v from w.
* Prove that if a factors over B then a is a square if and only
  if the 'vector' v is 0.
-/

example : (3 : ℕ).Prime := by norm_num

@[ext]
structure FactorBase where
  n : ℕ
  B : Fin n → ℤ
  correct : ∀ (i : Fin n), B i = -1 ∨ (0 < B i ∧ (B i).natAbs.Prime)
  injb : B.Injective

def factors_over (a : ℤ) (f : FactorBase) :=
  ∀ p : ℕ, p.Prime → (p : ℤ) ∣ a → ∃ i : Fin (f.n), p = f.B i

/-
Next thoughts:

Want structure ExponentVector

Want functions

  P : (a : ℤ) → ExponentVector

  Q : (e : ExponentVector)  → ℤ

and results

for all f, for all a, if a factors over f, then Q f (P f a) = a
for all f, for all e, P f (Q f e) = e

*or* functions

  P : (f : FactorBase) (a : ℤ) (h : factors_over a f) → ExponentVector

  Q : (f : FactorBase) (e : ExponentVector)  → ℤ

and something equivalent to the above conditions.

-/


open Finsupp Nat

#eval (60 : ℕ).factorization

/-
Informally, a finitely supported function is a function f : A → B
and a finite set S of elements of A such that

f(a) = 0 ↔ a ∉ S

-/

@[ext]
structure ExponentVector where
  f : FactorBase
  w : Fin f.n → ℕ

def Q (e : ExponentVector) : ℤ :=
  ∏ i, (e.f.B i) ^ (e.w i)

def P (f : FactorBase) (a : ℤ) : ExponentVector where
  f := f
  w := fun i =>
    let p := f.B i
    if p = -1 then
      if a < 0 then
        1
      else 0
    else padicValNat p.natAbs a.natAbs

def fbase : FactorBase where
  n := 3
  B := ![-1, 2, 3]
  correct := by
    intro i
    fin_cases i
    all_goals norm_num
  injb := by
    refine List.nodup_ofFn.mp ?_
    simp

def expvec : ExponentVector where
  f := fbase
  w := ![1, 4, 2]

#eval (P expvec.f (Q expvec)).w


example (e : ExponentVector) : P e.f (Q e) = e := by
  ext
  · unfold P Q
    simp
  · unfold P Q
    simp
  unfold P Q
  simp
  ext x
  split_ifs with h₁ h₂
  · sorry
  · sorry
  sorry

def Int.exponentVector (z : ℤ) : ℤ →₀ ℕ where
  support :=
    if z = 0 then ∅
    else
      let s : Finset ℤ := (z.natAbs.primeFactors : Finset ℕ).image (↑)
      if z < 0 then insert (-1) s else s
  toFun p :=
    if z = 0 then 0
    else if p = -1 then if z < 0 then 1 else 0
    else if p < 0 then 0
    else if p.natAbs.Prime then padicValNat p.natAbs z.natAbs else 0
  mem_support_toFun := by
    intro p
    simp
    split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    any_goals simp
    · simpa
    · aesop
    · simpa [h7]
    · apply And.intro h7
      intro q hq hqdiv hzne qep
      rw [←qep] at h8
      exact (Int.natCast_nonneg q).not_gt h8
    · constructor
      · rintro (peq | ⟨q, ⟨qprime, ddiv, -⟩, qep⟩)
        · contradiction
        simp [*]
        constructor
        · exact Nat.Prime.ne_one h9
        rwa [←qep, Int.ofNat_dvd_left]
      simp
      rintro - - - pdiv
      right
      use p.natAbs
      simp [*, Int.not_lt.mp]
    · aesop
    · aesop
    · rintro q qprime pdiv - qep
      rw [←qep] at h11
      exact (Int.natCast_nonneg q).not_gt h11
    · constructor
      · rintro ⟨q, ⟨qprime, qdiv, -⟩, qeqp⟩
        have pdiv : p ∣ z := by
          rw [←qeqp]
          exact ofNat_dvd_left.mpr qdiv
        aesop
      rintro ⟨-, pne, -, pdiv⟩
      use p.natAbs
      aesop
    · rintro q hq qdiv qeqp
      aesop

#eval (-60 : ℤ).exponentVector

example (q : ℕ) (z : ℤ) (h : q ∣ z.natAbs) : (q : ℤ) ∣ z := by exact Int.ofNat_dvd_left.mpr h

example (p : ℤ) (h : 0 ≤ p) : p.natAbs = p := by exact Int.natAbs_of_nonneg h

def Int.exponentVector2 (z : ℤ) : ℤ →₀ ℕ where
  support :=
      let s : Finset ℤ := (z.natAbs.factorization.support : Finset ℕ).image (↑)
      if z < 0 then insert (-1) s else s
  toFun p :=
    if p = -1 then if z < 0 then 1 else 0
    else if p < 0 then 0
    else (z.natAbs).factorization.toFun p.natAbs
  mem_support_toFun := by
    intro p
    simp
    split_ifs with h1 h2 h3 h4 h5
    · aesop
    · simp [*] -- maybe do this differently
      rintro q - - - rfl
      exact (Int.natCast_nonneg q).not_gt h3
    · suffices hsupp : p.natAbs ∈ z.natAbs.primeFactors ↔
        ¬ z.natAbs.factorization.toFun p.natAbs = 0
      · rw [←hsupp]
        simp [h2]
        constructor
        · rintro ⟨q, ⟨_, qdiv, _⟩, rfl ⟩
          simp [*]
          exact Int.ofNat_dvd_left.mpr qdiv
        rintro ⟨hp, pdiv, zne⟩
        use p.natAbs
        simp [*]
        linarith
      apply z.natAbs.factorization.mem_support_toFun
    · aesop
    · simp
      rintro q - - - rfl
      exact (Int.natCast_nonneg q).not_gt h5
    suffices hsupp : p.natAbs ∈ z.natAbs.primeFactors ↔
        ¬ z.natAbs.factorization.toFun p.natAbs = 0
    · rw [←hsupp]
      have pnn : 0 ≤ p := by linarith [h5]
      simp
      constructor
      · rintro ⟨q, ⟨⟨hq, qdiv, zne⟩, rfl⟩⟩
        simp [Int.ofNat_dvd_left.mpr qdiv, hq, zne]
      rintro ⟨hp, pdiv, zne⟩
      use p.natAbs
      aesop
    rw [show z.natAbs.factorization.toFun p.natAbs = z.natAbs.factorization p.natAbs from rfl]
    rw [iff_not_comm, factorization_eq_zero_iff]
    simp
    constructor
    · aesop
    intro h
    -- The remainder of the proof is purely by logic. Can this be automated?
    by_cases hp : Nat.Prime p.natAbs
    · right
      specialize h hp
      by_cases hdiv : p ∣ z
      · right
        exact h hdiv
      left
      exact hdiv
    left
    exact hp

example (p q : Prop) : (p ↔ q) ↔ (¬p ↔ ¬q) := by exact Iff.symm not_iff_not

#eval Int.exponentVector (-44)

open BigOperators

def valueFromExponentVector (ev : ℤ →₀ ℕ) : ℤ :=
  ∏ p ∈ ev.support, p ^ ev p

def valueFromExponentVector2 (ev : ℤ →₀ ℕ) : ℤ :=
  ev.prod (· ^ ·)

#eval valueFromExponentVector ((-44 : ℤ).exponentVector)


#check factorization_prod_pow_eq_self

#check Finset.prod

example (n : ℕ) (h : n ≠ 0) : ∏ p ∈ n.primeFactors, p ^(n.factorization p) = n := by
  nth_rw 3 [←Nat.factorization_prod_pow_eq_self h]
  simp [prod]

example (a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) : a.natAbs = b.natAbs ↔ a = b:= by
  exact (Int.natAbs_inj_of_nonneg_of_nonneg ha hb)


example (S : Finset ℕ ) (f : ℕ → ℤ) (h : ∀ x ∈ S, 0 ≤ f x) :
  0 ≤ ∏ x ∈ S, f x := by
  exact Finset.prod_nonneg h

example (z : ℤ) (hz : z ≠ 0) : z.natAbs ≠ 0 := by exact Int.natAbs_ne_zero.mpr hz

example (z : ℤ) : |z|.natAbs = z.natAbs := by exact Int.natAbs_abs z

example (z : ℤ) (hz : z ≠ 0) : valueFromExponentVector (z.exponentVector2) = z := by
  unfold valueFromExponentVector Int.exponentVector2
  simp [*]
  split_ifs with zlt
  · simp
    have zeq : z = -z.natAbs := by
      refine Int.eq_neg_natAbs_of_nonpos ?_
      linarith
    nth_rw 3 [zeq]
    simp
    rw [←Int.natAbs_inj_of_nonneg_of_nonneg]
    rw [Int.natAbs_abs z]
    · have : (∏ x ∈ z.natAbs.primeFactors, if (x : ℤ) < 0 then 1 else (x : ℤ) ^ z.natAbs.factorization.toFun x)
        = (∏ x ∈ z.natAbs.primeFactors, x ^ z.natAbs.factorization x) := by
        norm_cast
      rw [this]
      clear this
      norm_cast
      have hzabsn : z.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hz
      nth_rw 3 [←Nat.factorization_prod_pow_eq_self hzabsn]
      simp [prod]
    · apply Finset.prod_nonneg
      intro i iin
      split_ifs
      · linarith
      simp
    exact abs_nonneg z
  have zeq : z.natAbs = z := by
    refine Int.natAbs_of_nonneg ?_
    linarith
  nth_rw 3 [←zeq]
  simp
  rw [←Int.natAbs_inj_of_nonneg_of_nonneg]
  rw [Int.natAbs_abs z]
  · have : (∏ x ∈ z.natAbs.primeFactors, if (x : ℤ) < 0 then 1 else (x : ℤ) ^ z.natAbs.factorization.toFun x)
        = (∏ x ∈ z.natAbs.primeFactors, x ^ z.natAbs.factorization x) := by
        norm_cast
    rw [this]
    clear this
    norm_cast
    have hzabsn : z.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hz
    nth_rw 3 [←Nat.factorization_prod_pow_eq_self hzabsn]
    simp [prod]
  · apply Finset.prod_nonneg
    intro i iin
    split_ifs
    · linarith
    simp
  exact abs_nonneg z
