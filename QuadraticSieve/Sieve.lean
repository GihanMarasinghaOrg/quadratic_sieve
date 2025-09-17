import Mathlib

def PrimeList := {l : List ℕ | ∀ p ∈ l, Nat.Prime p}

def Q (x n : ℤ) : ℤ := x^2 - n

def IsNicePrime (p : ℕ) (n : ℤ) : Bool :=
  if Nat.Prime p ∧ jacobiSym n p = 1 then True
  else False

def FBase (B : ℕ) (n : ℤ) : List ℕ :=
  (List.range (B + 1)).filter (fun p => IsNicePrime p n)

#eval FBase 30 1007

/-- `floorSqrtAux n lo hi` is an auxiliary binary-search function returning the largest `m` in `[lo, hi)` such that `m * m ≤ n`. -/
def floorSqrtAux (n lo hi : Nat) : Nat :=
  if hi ≤ lo + 1 then lo
  else
    let mid := (lo + hi) / 2
    if mid * mid ≤ n then
      floorSqrtAux n mid hi
    else
      floorSqrtAux n lo mid

/-- `floorSqrt n` computes the floor of the square root of `n` by a binary search on natural numbers. -/
def floorSqrt (n : Nat) : Nat :=
  floorSqrtAux n 0 (n + 1)

#eval floorSqrt 64

def QValues (n : ℕ) (Y : ℕ) : List ℤ :=
  List.range (2 * Y + 1)
    |>.map (fun i => Q (floorSqrt n + (i - Y)) n)

#eval QValues 1007 5

def divideIfDivisible (m p : ℤ) : ℤ :=
  if m % p = 0 then m / p else m

/-
`f` takes a list of integers `x` and an integer `p`. It returns a modified
version of `x` in which all the elements of `x` that are divisible by `p` have
been divded by `p`.
-/
def f (x : List ℤ) (p : ℤ) : List ℤ :=
  x.map (fun e => divideIfDivisible e p)

#eval f (QValues 1007 5) 2

#eval f (f (QValues 1007 5) 2) 17

#eval (FBase 30 1007).foldl f (QValues 1007 5)

/-
divlistbyfbase produces the last element in a sequence of lists, indexed by elements of `fb`, where
each list is constructed from the previous element by dividing each element in the list by the
indexed element of `fb`. The sequence of lists starts with `x`.
-/
def divlistbyfbase (fb x : List ℤ) := fb.foldl f x

def divbyfbaseQ (B n Y : ℕ) := divlistbyfbase (FBase B n) (QValues n Y)

#eval divbyfbaseQ 30 1007 5

/-
`divByAll` takes an integer `a` and a list `fb` of integers and successively divides `a` by the
elements of `fb` (when `a` is divisible by that element of `fb`).
-/
def divByAll (a : ℤ) (fb : List ℤ) : ℤ :=
  fb.foldl divideIfDivisible a

/-
divlistbyfbase2 produces the last element in a sequence of lists, indexed by elements of `x`, where
each list is constructed from the previous list by dividing the indexed element of `x` by *all*
the elements of `fb`.
-/
def divlistbyfbase2 (fb x : List ℤ) := x.map (fun a => divByAll a fb)

def divbyfbaseQ2 (B n Y : ℕ) := divlistbyfbase2 (FBase B n) (QValues n Y)

#eval divbyfbaseQ2 30 1007 5

/-- Apply a single "factor" `a : α` elementwise to a list `xs : List β`
    using an action `g : β → α → β`. -/
def updateAll {α β} (g : β → α → β) (xs : List β) (a : α) : List β :=
  xs.map (fun e => g e a)

/-- Apply all factors `fb : List α` to a single element `b : β`
    by folding with `g`. -/
def applyAll {α β} (g : β → α → β) (b : β) (fb : List α) : β :=
  fb.foldl g b

/-- Fold over the factor base, updating the whole list at each step. -/
def foldUpdateAll {α β} (g : β → α → β) (fb : List α) (xs : List β) : List β :=
  fb.foldl (updateAll g) xs

/-- Map once, applying the whole factor base to each element. -/
def mapApplyAll {α β} (g : β → α → β) (fb : List α) (xs : List β) : List β :=
  xs.map (fun b => applyAll g b fb)

/-- General commutation: folding "elementwise updates" over `fb` equals
    mapping "fold all factors" once. -/
lemma foldUpdateAll_eq_mapApplyAll {α β}
    (g : β → α → β) (fb : List α) (xs : List β) :
    foldUpdateAll g fb xs = mapApplyAll g fb xs := by
  induction fb generalizing xs with
  | nil =>
      simp [foldUpdateAll, mapApplyAll, applyAll]
  | cons p ps ih =>
      -- Apply IH to the list after doing the first update by `p`
      have h := ih (xs.map (fun e => g e p))
      simpa [foldUpdateAll, mapApplyAll, applyAll, updateAll, List.map_map] using h

lemma divlistbyfbase_eq_divlistbyfbase2 (fb x : List ℤ) :
    divlistbyfbase fb x = divlistbyfbase2 fb x := by
  simpa [divlistbyfbase, divlistbyfbase2, f, divByAll]
    using foldUpdateAll_eq_mapApplyAll divideIfDivisible fb x

/-
`signIndices xs` returns the list of indices `i` for which `xs[i] = 1` or `xs[i] = -1`.
- Uses `List.enum` to pair each element with its index, then filters and extracts the index.
-/
/- def signIndices (xs : List Int) : List Nat :=
  xs.enum
    |>.filterMap fun ⟨i, x⟩ =>
      if x = 1 ∨ x = -1 then
        some i
      else
        none

#eval signIndices ((FBase 30 1007).foldl f (QValues 1007 5)) -/

/- def relationIndices (B n Y : ℕ) :=
  signIndices (divbyfbaseQ B n Y)

#eval relationIndices 30 1007 5 -/

/-
Question: is it the case, for each i in `relationIndices B n Y` that
`(QValues n B)[i]` factors over FBase B n?
-/

/- def divbypowers : ℕ → ℕ → ℕ
  | 0, _ => 0
  | _+1, 0 => 0
  | n+1, 1 => n + 1
  | n+1, k + 2 =>
    if h : (n+1) % (k + 2) = 0 then
      divbypowers ((n+1) / (k + 2)) (k + 2)
    else
      n+1
decreasing_by
  exact Nat.div_lt_self (Nat.succ_pos n) (Nat.one_lt_succ_succ k) -/

/--
a divided by (p raised to the p-adic valuation of a)
-/
def divbypowers (a p : ℕ) : ℕ :=
  a / p^(padicValNat p a)

lemma divbypowers_powp (i p : ℕ) [Fact p.Prime] : divbypowers (p ^ i) p = 1 := by
  dsimp [divbypowers]
  rw [padicValNat.prime_pow]
  rw [Nat.div_self]
  have h : 0 < p := Nat.Prime.pos (Fact.out : p.Prime)
  apply pow_pos h

#eval divbypowers 150 5
#eval divbypowers 10 0

@[simp]
def factorisableOver : (List Nat) → Nat → Bool
  | _ :: []  , 1 => true
  | p :: []  , n => divbypowers n p == 1
  | p :: tail , n => factorisableOver tail (divbypowers n p)
  | []    , _ => true

#eval factorisableOver [5] 15
#eval factorisableOver [2, 5, 7] 14

def factorisableOverInt (fb : List Nat) (z : Int) : Bool :=
  factorisableOver fb z.natAbs

#eval factorisableOverInt [2, 3, 5] (-60)  -- true, since 60 = 2*2*3*5
#eval factorisableOver [2, 3, 5] 14  -- false, since 7 ∉ [2,3,5]
#eval factorisableOver [] 14  -- f

lemma factorisableOverEmpty (n : ℕ) : factorisableOver [] n = true := by
  simp

lemma factorisableOverConsCons (n p q : ℕ) (tail : List ℕ) :
  factorisableOver (p :: q :: tail) n = factorisableOver (q :: tail) (divbypowers n p) := by
  by_cases h2 : n = 1
  · simp [h2]
  by_cases htail : tail = []
  all_goals simp [htail]

lemma factorisableOver_listp (n p : ℕ) (h : divbypowers n p = 1) : factorisableOver [p] n := by
  by_cases h2 : n = 1
  · simp [h2]
  simp [h]

/-
Let `x` be an integer. Let `y` be `divByAll x fb`, i.e. the result of dividing `x` by all the
elements of the list `fb` which divide `x`. Is is the case that if `y` is `+1` or `-1`, then
`factorisableOverInt fb x`?
-/

#eval ["Bob", "Jim"].zip [2, 4]

lemma natAbs_mod_eq_zero_of_mod_eq_zero (x : ℤ) (p : ℕ) (h : x % p = 0) : x.natAbs % p = 0 := by
  rw [←Nat.dvd_iff_mod_eq_zero]
  rw [EuclideanDomain.mod_eq_zero] at h
  rw [←Int.dvd_natAbs] at h
  norm_cast at h

example (x : ℕ) (p : ℕ) : x % p = 0 ↔ p ∣ x := by exact Iff.symm Nat.dvd_iff_mod_eq_zero

example (x : ℤ) (p : ℤ) : x % p = 0 ↔ p ∣ x := by exact EuclideanDomain.mod_eq_zero


#check Int.dvd_natAbs

lemma foo (x p : ℕ) (fb : List ℕ) (h : divByAll x (p :: fb) = 1)
   : divByAll (divbypowers x p) fb = 1 := by
  sorry


def divideIfDivisibleNat (m p : ℕ) : ℕ :=
  if m % p = 0 then m / p else m

example (x p : ℕ) (h : x ≠ 0) : p * p ^ (x - 1) = p ^ x := by exact mul_pow_sub_one h p

lemma nat_div_eq_one_coe (a b : ℕ) (hb : (b : ℝ) ≠ 0)
    (h : (a : ℝ) / (b : ℝ) = 1) : a = b := by
  field_simp [hb] at h
  norm_cast at h


lemma Nat.eq_of_div_eq_one {a k : ℕ} (hk : k ∣ a) (h : a / k = 1) : a = k := by
  have := Nat.div_mul_cancel hk
  rw [h, Nat.one_mul] at this
  symm at this
  exact this

lemma Int.eq_of_ediv_eq_one {a k : ℤ} (hk : k ∣ a) (h : a / k = 1) : a = k := by
  have := Int.ediv_mul_cancel hk
  rw [h, one_mul] at this
  symm at this
  exact this

/-
Counterexample to the following if not all the elements of fb are prime

#eval factorisableOver [10] 10

#eval factorisableOver [10] 5
-/

example (p : ℕ) (h : p.Prime) : 0 < p := by exact Nat.Prime.pos h

lemma padicvalnat_le (a b p : ℕ) (hp : Fact p.Prime) (h₁ : b ∣ a) (hₐ : a ≠ 0) :
    padicValNat p b ≤ padicValNat p a := by
  rcases h₁ with ⟨c, rfl⟩
  rw [padicValNat.mul]
  exact Nat.le_add_right (padicValNat p b) (padicValNat p c)
  exact (Nat.mul_ne_zero_iff.mp hₐ).1
  exact (Nat.mul_ne_zero_iff.mp hₐ).2


lemma div_eq_of_mul_eq {a b c : ℕ} (h : a = b * c) (h₁ : 0 < b) : a / b = c := by
  have hdiv : b ∣ a := by rw [h]; exact Nat.dvd_mul_right b c
  rw [h, mul_comm]
  apply Nat.mul_div_cancel
  exact h₁

lemma tod {p a c : ℕ} [Fact p.Prime] (h : c ∣ divbypowers a p) : c ∣ a := by sorry

lemma geoff {p b x : ℕ} [Fact p.Prime] :
  divbypowers (b * p ^ x) p= divbypowers b p := by sorry

lemma gwendoline {p c a : ℕ} [Fact p.Prime] (hc : gcd c p = 1) (hcdvd : c ∣ a) :
  (divbypowers a p) / c = divbypowers (a / c) p := by sorry


/- lemma jane (a p c x : ℕ) [Fact p.Prime] (hc : gcd c p = 1)
  (hcdvd : c ∣ divbypowers a p)
    :
  (divbypowers a p / c) * p ^ x =
  (divbypowers (divbypowers a p / c * p ^ x) p) := by
  have hcadvd : c ∣ a := tod hcdvd

  rw [geoff, gwendoline hc hcadvd]

  --unfold divbypowers


  sorry -/

lemma eq_pow_padicValNat_of_factorisableOverSingleton {p a : ℕ} (h : factorisableOver [p] a)
    : a = p ^ (padicValNat p a) := by
  by_cases hane : a = 1
  · rw [hane, padicValNat.one, pow_zero]
  simp [factorisableOver, divbypowers] at h
  exact Nat.eq_of_div_eq_one pow_padicValNat_dvd h


/-
The lemma below is false with our current definition of factorisableOver as

factorisableOver [] d

is true for any d

Perhaps

factorisableOver [] d

should be false instead. Or maybe not.
-/

lemma factorisableOver_mul_prime_pow (d p x : ℕ) (bs : List ℕ) [Fact p.Prime]
  (h : factorisableOver bs d) : factorisableOver (p :: bs) (d * p ^ x) := by
    induction bs with
    | nil =>
      sorry
    | cons q tail ih =>
      sorry

example (a : ℕ) (h : 0 < a ) : a / a = 1 := by
  refine div_eq_of_mul_eq ?_ ?_
  rw [mul_one]
  exact h

lemma prime_pow_ne_zero {p y : ℕ} [Fact p.Prime] : p ^ y ≠ 0 :=
  pow_ne_zero y (Ne.symm (NeZero.ne' p))

lemma factorisableOver_mul_prime_pow₂  (d p x b : ℕ) (bs : List ℕ) [Fact p.Prime] [Fact b.Prime]
  (h : factorisableOver (b :: bs) d) : factorisableOver (p :: b :: bs) (d * p ^ x) := by
    induction bs with
    | nil =>
      dsimp [factorisableOver]
      have h₂ := eq_pow_padicValNat_of_factorisableOverSingleton h
      rw [h₂, divbypowers]
      by_cases hbeqp : b = p
      · rw [hbeqp]
        rw [←pow_add, padicValNat.prime_pow]
        suffices h₃ : p ^ (padicValNat p d + x) / p ^ (padicValNat p d + x) = 1
        · rw [h₃]
          simp
        refine div_eq_of_mul_eq ?_ ?_
        rw [mul_one]
        apply Nat.pos_of_ne_zero
        apply prime_pow_ne_zero
      have h₃ : padicValNat p (b ^ padicValNat b d * p ^ x) = x := by
        /-
        we need to use

          padicValNat_mul_pow_left

        to complete this
        -/
        sorry
      rw [h₃, ←h₂]
      rw [Nat.mul_div_cancel]
      · exact h
      apply Nat.pos_of_ne_zero
      apply prime_pow_ne_zero
    | cons q tail ih =>
      sorry

lemma div_pow_eq_pow_sub_of_padicValNat {p a b : ℕ} (hbdvd : b ∣ a) (hanon : a ≠ 0) [Fact p.Prime] :
  p ^ (padicValNat p a)  / p ^ (padicValNat p b)
    = p ^ (padicValNat p a - padicValNat p b) := by
  apply Nat.pow_div
  · rcases hbdvd with ⟨m, rfl⟩
    have h2 : padicValNat p (b * m)  = padicValNat p b + padicValNat p m := by
      have h3 : b ≠ 0 ∧ m ≠ 0 := Nat.mul_ne_zero_iff.mp hanon
      apply padicValNat.mul h3.1 h3.2
    rw [h2]
    apply Nat.le_add_right
  exact Nat.Prime.pos (Fact.out : p.Prime)

lemma not_dvd_of_dvd_mul_padicValNat {c b p : ℕ} [Fact p.Prime] (h : b = c * (p ^ padicValNat p b)) (hb : b ≠ 0) : ¬ p ∣ c := by
  intro hpc
  rw [dvd_def] at hpc
  obtain ⟨k, hk⟩ := hpc
  rw [hk, mul_comm, ← mul_assoc, ← Nat.pow_succ, Nat.succ_eq_add_one] at h
  have hpowdvd : p ^ (padicValNat p b + 1) ∣ b := by
    use k
  have hle : padicValNat p b + 1 ≤ padicValNat p b := by
    apply (padicValNat_dvd_iff_le hb).1
    exact hpowdvd
  apply Nat.not_succ_le_self (padicValNat p b)
  rw [Nat.succ_eq_add_one]
  exact hle

lemma dvd_nonzero_of_dvd_ne_zero {a b : ℕ} (ha : a ≠ 0) (h : b ∣ a) : b ≠ 0 := by
  intro hb
  rw [hb] at h
  obtain ⟨k, hk⟩ := h
  simp at hk
  exact ha hk

lemma divbypowers_pos (a p : ℕ) (hp : p.Prime) (hanon : a ≠ 0) : 0 < divbypowers a p := by
  unfold divbypowers
  have hpnon : p ≠ 0 := by exact Nat.Prime.ne_zero hp
  have hppnon : p ^ padicValNat p a ≠ 0 := by exact pow_ne_zero (padicValNat p a) hpnon
  have hpppnon : a / p ^ padicValNat p a ≠ 0 := by
    refine (Nat.div_ne_zero_iff_of_dvd ?_).mpr ?_
    exact pow_padicValNat_dvd
    constructor
    exact hanon
    exact hppnon
  exact Nat.zero_lt_of_ne_zero hpppnon


lemma tail_inherits {α : Type*} (P : α → Prop) (head : α) (tail : List α)
  (h : ∀ x ∈ head :: tail, P x) : ∀ y ∈ tail, P y := by
    intro y ytail
    have hmem : y ∈ head :: tail := by
      apply List.mem_cons_of_mem
      exact ytail
    apply h
    exact hmem




lemma factorisable_over_dvd (a b : ℕ) (fb : List ℕ) (hapos : 0 < a)
  (h₁ : b ∣ a) (h₂ : factorisableOver fb a)
  (fbp : ∀ q ∈ fb, q.Prime) : factorisableOver fb (a/b) := by
    induction fb generalizing a b with
  | nil =>
    simp [factorisableOver]
  | cons p tail ih =>
    cases tail with
    | nil =>
      by_cases ha : a = 1
      subst ha
      have hb : b = 1 := by
        exact Nat.eq_one_of_dvd_one h₁
      subst hb
      norm_num
      have h₃ : (p ^ padicValNat p a) ≠ 0 := by
        by_cases hp : p = 0
        simp [hp]
        exact pow_ne_zero (padicValNat p a) hp
      have h₅ : a = p ^ padicValNat p a := eq_pow_padicValNat_of_factorisableOverSingleton h₂
      have h₆ : b ∣ p ^ padicValNat p a := by
        rw[← h₅]
        exact h₁
      have hp : p.Prime := by
        apply fbp
        rw [List.mem_singleton]
      haveI : Fact p.Prime := ⟨hp⟩
      rw [Nat.dvd_prime_pow hp] at h₆
      rcases h₆ with ⟨i, ⟨hkle, rfl⟩⟩
      by_cases hieq : i = 0
      · rw [hieq, pow_zero, Nat.div_one, h₂]
      by_cases hipad : i = padicValNat p a
      · rw [hipad, ←h₅, Nat.div_self hapos]
        rfl
      rw [h₅, Nat.pow_div hkle (Nat.Prime.pos hp)]
      by_cases hisone : p ^ (padicValNat p a - i) = 1
      · rw [hisone]
        rfl
      simp
      rw [divbypowers_powp]
    | cons r rs =>
      dsimp [factorisableOver] at h₂
      have hp : p.Prime := by
        apply fbp
        exact List.mem_cons_self
      haveI : Fact p.Prime := ⟨hp⟩
      have haeq : a = (divbypowers a p) * (p ^ padicValNat p a) := by
        simp [divbypowers]
        symm
        apply Nat.div_mul_cancel
        exact pow_padicValNat_dvd
      let c := b / (p ^ padicValNat p b)
      have hceq : c = b / (p ^ padicValNat p b) := by exact rfl
      have hbeq : b = c * (p ^ padicValNat p b) := by
        rw [hceq]
        symm
        apply Nat.div_mul_cancel
        exact pow_padicValNat_dvd
      have hk : ∃ k : ℕ, a = b * k := by exact h₁
      obtain ⟨k, habk⟩ := hk
      rw [haeq, hbeq] at habk
      have hanon : a ≠ 0 := by exact Nat.ne_zero_of_lt hapos
      have hpdvd : (p ^ padicValNat p b) ∣ (p ^ padicValNat p a) := by
        apply Nat.pow_dvd_pow
        apply padicvalnat_le
        exact this
        exact h₁
        exact hanon
      rw [dvd_def] at hpdvd
      obtain ⟨m, hm⟩ := hpdvd
      rw [hm] at habk
      have hpbnon : p ^ padicValNat p b ≠ 0 := by
        exact Ne.symm (NeZero.ne' (p ^ padicValNat p b))
      rw [mul_comm, mul_comm c (p ^ padicValNat p b),
      mul_assoc, mul_assoc (p ^ padicValNat p b) c k] at habk
      have hcancel : m * divbypowers a p = c * k := by
        exact (Nat.mul_right_inj hpbnon).mp habk
      have hc : c ∣ m * divbypowers a p := by
        exact Dvd.intro k (id (Eq.symm hcancel))
      have hmeq : (p ^ padicValNat p a) / (p ^ padicValNat p b) = m := by
        apply div_eq_of_mul_eq
        exact hm
        apply Nat.pow_pos
        apply Nat.Prime.pos hp
      symm at hmeq
      have hmeq₂ : m = p ^ (padicValNat p a - padicValNat p b) := by
        rw [hmeq]
        apply div_pow_eq_pow_sub_of_padicValNat h₁ hanon
      have hnpdvdc : ¬ p ∣ c := by
        apply not_dvd_of_dvd_mul_padicValNat
        exact hbeq
        apply dvd_nonzero_of_dvd_ne_zero hanon h₁
      have hcdiv : c ∣ divbypowers a p := by
        have hpc : p.Coprime c := by
          apply (Nat.Prime.coprime_iff_not_dvd hp).2
          exact hnpdvdc
        have hmc : m.Coprime c := by
          rw [hmeq₂]
          apply Nat.gcd_pow_left_of_gcd_eq_one
          exact hpc
        apply Nat.Coprime.dvd_of_dvd_mul_left
        apply (Nat.coprime_comm).1
        exact hmc
        exact hc
      have hrfac : factorisableOver (r :: rs) (divbypowers a p / c) := by
        apply ih
        apply divbypowers_pos
        exact hp
        exact hanon
        exact hcdiv
        exact h₂
        intro q hq
        apply tail_inherits Nat.Prime p (r :: rs) fbp
        exact hq
      rw [haeq, hbeq]
      have hmul : divbypowers a p * p ^ padicValNat p a / (c * p ^ padicValNat p b) =
        (divbypowers a p / c) * (p ^ padicValNat p a /  p ^ padicValNat p b) := by sorry
      rwa [hmul, ←hmeq, hmeq₂, factorisableOver_mul_prime_pow]







#eval divByAll 10 [5]

#check List.mem_cons_of_mem


lemma factorisable_of_divisble2 (fb : List ℕ) :
  ∀ (x : ℤ), (divByAll x fb) = 1 → factorisableOverInt fb x := by
  induction fb with
  | nil =>
      intro x h
      dsimp [factorisableOverInt]
  | cons p tail ih =>
      dsimp [factorisableOverInt, factorisableOver]
      induction tail with
      | nil =>
          intro x h
          dsimp [divByAll] at h
          simp at h
          dsimp [divideIfDivisible] at h
          by_cases hx : x % p = 0
          · simp [hx] at h
            have h2 : divbypowers x.natAbs p = 1 := by
              dsimp [divbypowers]
              have hdiv : ↑p ∣ x := Int.dvd_of_emod_eq_zero hx
              have h3 : x = ↑p := Int.eq_of_ediv_eq_one hdiv h
              have hnat : x.natAbs = p := by
                rw [h3]
                exact rfl
              rw [hnat]
              sorry
            apply factorisableOver_listp
            exact h2
          simp [hx] at h
          simp [h]
      | cons q tail2 =>
          intro y hy
          simp at hy
          rw [factorisableOverConsCons]
          specialize ih (divbypowers y.natAbs p)
          apply ih

          /- See the Ideas.lean file for how to proceed. -/
          sorry


theorem roo (B n Y : ℕ) : ∀ pa ∈ (divbyfbaseQ B n Y).zip (QValues n Y),
  pa.fst = 1 ∨ pa.fst = -1 → factorisableOverInt (FBase B n) pa.snd := by
  intro ⟨p, q⟩ hp

  sorry




def fGen {α β : Type} (op : α → β → α) (xs : List α) (p : β) : List α :=
  xs.map (fun e => op e p)

def divByAllGen {α β : Type} (op : α → β → α) (a : α) (fb : List β) : α :=
  fb.foldl op a

def divlistbyfbaseGen {α β : Type} (op : α → β → α) (fb : List β) (x : List α) : List α :=
  fb.foldl (fGen op) x

def divlistbyfbase2Gen {α β : Type} (op : α → β → α) (fb : List β) (x : List α) : List α :=
  x.map (fun a => divByAllGen op a fb)

lemma divlistbyfbaseGen_eq_divlistbyfbase2Gen
  {α β : Type} (op : α → β → α) (fb : List β) (x : List α) :
  divlistbyfbaseGen op fb x = divlistbyfbase2Gen op fb x := by
  induction fb generalizing x with
  | nil =>
      simp [divlistbyfbaseGen, divlistbyfbase2Gen, divByAllGen]
  | cons p ps ih =>
      simp [divlistbyfbaseGen, divlistbyfbase2Gen, fGen, divByAllGen, List.foldl]
      have h := ih (x.map (fun a => op a p))
      rw [divlistbyfbaseGen, divlistbyfbase2Gen] at h
      simp [divByAllGen, List.map_map] at h
      exact h

def newf := fGen divideIfDivisible

def newdivByAlldivByAll := divByAllGen divideIfDivisible

def newdivlistbyfbase := divlistbyfbaseGen divideIfDivisible

def newdivlistbyfbase2 := divlistbyfbase2Gen divideIfDivisible

lemma newdivlistbyfbase_eq_newdivlistbyfbase2 (fb x : List ℤ) :
  divlistbyfbase fb x = divlistbyfbase2 fb x :=
  divlistbyfbaseGen_eq_divlistbyfbase2Gen divideIfDivisible fb x
