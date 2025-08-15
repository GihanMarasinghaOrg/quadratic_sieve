import Mathlib

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

/--
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

def divbypowers (a p : ℕ) : ℕ :=
  a / p^(padicValNat p a)

#eval divbypowers 150 5

@[simp]
def factorisableOver : (List Nat) → Nat → Bool
  | _ :: []  , 1 => true
  | p :: []  , n => n % p == 0
  | p :: tail , n => factorisableOver tail (divbypowers n p)
  | []    , _ => true

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

lemma factorisableOver_listp (n p : ℕ) (h : n % p = 0) : factorisableOver [p] n := by
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

example (x p : ℕ) (h : x ≠ 0): p * p ^ (x - 1) = p ^ x := by exact mul_pow_sub_one h p
/-
lemma divbypowers_idem (a p : ℕ)
    (hp : Nat.Prime p) :
    divbypowers (if p ∣ a then a / p else a) p = divbypowers a p := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  unfold divbypowers
  by_cases h : p ∣ a
  · -- `p | a` case: one division reduces the valuation by exactly 1
    have hval :
        padicValNat p (a / p) = (padicValNat p a) - 1 := padicValNat.div h -- see note below
    -- now just rewrite the exponents

    have : p ^ (padicValNat p (a / p)) = p ^ (padicValNat p a - 1) := by
      simpa [hval]
    simp [h, this, Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm, Nat.mul_left_comm,
          Nat.mul_assoc, Nat.one_mul, Nat.sub_add_cancel (Nat.succ_le_of_lt hp.one_lt)]
    have h2 : padicValNat p a ≠ 0 := by
      rw [←dvd_iff_padicValNat_ne_zero]
      · exact h


  · -- `p ∤ a` case: the `if` is a no-op and the valuation is 0
    have : padicValNat p a = 0 := by
      apply padicValNat.eq_zero_of_not_dvd h
      --padicValNat.eq_zero_of_not_dvd (by simpa using h) hp.ne_one
    simp [h, this]

  done -/

/-
lemma foo_coprime
  (x p : ℕ) (fb : List ℕ)
  (hp : 2 ≤ p) -- or `Nat.Prime p`
  (hc : ∀ q ∈ fb, Nat.Coprime p q)
  (h : divByAll x (p :: fb) = 1) :
  divByAll (divbypowers x p) fb = 1 := by
  -- idea:
  -- 1) Rewrite `h` via `List.foldl` to say:
  --       List.foldl divideIfDivisible (divideIfDivisible x p) fb = 1
  -- 2) Use the commutation lemma below (coprime case) to push
  --    `divbypowers · p` through each `divideIfDivisible · q` for `q ∈ fb`:
  --       divbypowers (List.foldl divideIfDivisible (divideIfDivisible x p) fb) p
  --     = List.foldl divideIfDivisible (divbypowers (divideIfDivisible x p) p) fb
  --     = List.foldl divideIfDivisible (divbypowers x p) fb
  -- 3) On the left, `h` gives the argument is `1`, and `divbypowers 1 p = 1`.
  -- 4) Conclude the right-hand side is `1`.
  --
  -- Implementation sketch:
  -- * Prove `divbypowers_idem` : `divbypowers (divideIfDivisible a p) p = divbypowers a p`.
  -- * Prove `commute_divbypowers_divOnce` for coprime `p q`:
  --       divbypowers (divideIfDivisible a q) p
  --     = divideIfDivisible (divbypowers a p) q
  -- * Then a fold-homomorphism lemma along the list `fb`.
  --
  -- See the lemmas stated just below; using them this closes in a few lines:
  have h1 :
      List.foldl divideIfDivisible (divideIfDivisible x p) fb = 1 := by
    simpa [divByAll, List.foldl] using h
  -- push `divbypowers · p` through the whole fold along `fb`
  have commute_fold :
      divbypowers (List.foldl divideIfDivisibleNat (divideIfDivisibleNat x p) fb) p
        = List.foldl divideIfDivisible (divbypowers (divideIfDivisibleNat x p) p) fb := by
    -- proved by induction on `fb` using `commute_divbypowers_divOnce`
    -- and `hc` to discharge `Coprime p q` at each step
    -- (see lemma stated below)
    exact commute_divbypowers_fold hp hc x p fb
  -- use `h1` on the LHS and idempotence wrt `p` on the RHS start
  have : List.foldl divideIfDivisible (divbypowers x p) fb = 1 := by
    -- `divbypowers 1 p = 1`
    have : divbypowers 1 p = 1 := divbypowers_one hp
    -- `divbypowers (divideIfDivisible x p) p = divbypowers x p`
    have idem : divbypowers (divideIfDivisible x p) p = divbypowers x p :=
      divbypowers_idem hp x p
    -- now rewrite the equality `commute_fold` using `h1`, `this`, and `idem`
    -- Left side becomes `divbypowers 1 p = 1`; right side is the target fold.
    simpa [divByAll, idem, this, h1]
      using commute_fold.symm
  simpa [divByAll] using this -/



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
            have h2 : x.natAbs % p = 0 := by
              apply natAbs_mod_eq_zero_of_mod_eq_zero
              exact hx
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
