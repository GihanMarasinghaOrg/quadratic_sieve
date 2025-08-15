import Mathlib

def divideIfDivisible (m p : ℤ) : ℤ :=
  if m % p = 0 then m / p else m

/-
`divByAll` takes an integer `a` and a list `fb` of integers and successively divides `a` by the
elements of `fb` (when `a` is divisible by that element of `fb`).
-/
def divByAll (a : ℤ) (fb : List ℤ) : ℤ :=
  fb.foldl divideIfDivisible a

def divbypowers (a p : ℕ) : ℕ :=
  a / p^(padicValNat p a)

@[simp]
def factorisableOver : (List Nat) → Nat → Bool
  | _ :: []  , 1 => true
  | p :: []  , n => n % p == 0
  | p :: tail , n => factorisableOver tail (divbypowers n p)
  | []    , _ => true

def factorisableOverInt (fb : List Nat) (z : Int) : Bool :=
  factorisableOver fb z.natAbs

lemma factorisable_of_divisble2 (fb : List ℕ) :
  ∀ (x : ℤ), (divByAll x fb) = 1 → factorisableOverInt fb x := by sorry

/-
Suppose fb is p :: tail. Suppose

∀ (x : ℤ), (divByAll x tail) = 1 → factorisableOverInt tail x

We must prove

∀ (x : ℤ), (divByAll x (p :: tail)) = 1 → factorisableOverInt (p :: tail) x

Assume y : ℤ. Assume (divByAll y (p :: tail)) = 1. We must show

 factorisableOverInt (p :: tail) y

Two cases: the tail is empty or it isn't. We can do induction on tail

Case 1: tail is empty. We must show

    factorisableOverInt (p :: []) y

  Either y = 1 or y ≠ 1.

  Case 1a) By definiton, factorisableOverInt (p :: []) 1 is true. Done!

  Case 1b)

    By definition, this is to show y % p = 0. We know (divByAll y [p]) = 1.
    As y ≠ 1, y is a positive power of p. So indeed y % p = 0.

Case 2: tail is q :: tail2. We must show

  ∀ (x : ℤ), (divByAll x (p :: q :: tail2)) = 1 → factorisableOverInt (p :: q :: tail2) x

  Let y : ℤ. Assume (divByAll y (p :: q :: tail2)) = 1. We must show

  factorisableOverInt (p :: q :: tail2) y.

  We have the inductive hypothesis

  ∀ (x : ℤ), (divByAll x (q ::tail2)) = 1 → factorisableOverInt (q :: tail2) x

  By definition,
  factorisableOverInt (p :: q :: tail2) y  =
      factorisableOverInt (q :: tail2) (divbypowers y p)

  So we must show

    factorisableOverInt (q :: tail2) (divbypowers y p)

  Either divByAll y (q :: tail2) = 1 or not.

  Case 2a)
    We then have factorisableOverInt (q :: tail2) y.

    Intuitively, for any a, b, fb, if b ∣ a, then

      factorisableOver fb a, then factorisableOver fg (a/b)

    The result follows (a is y and a/b is (divbypowers y p))

  Case 2b)

    Recall we must show

      `factorisableOverInt (q :: tail2) (divbypowers y p)`

    We are in the case `divByAll y (q :: tail2) ≠ 1`.

    We still have

      `(divByAll y (p :: q :: tail2)) = 1`.

    Intuitively, this means `y = pⁿ m` where `m` is `divbypowers y p` and
    that `divByAll m (q :: tail2) = 1`.

    **The above may require that the elements of the factor base are prime!**

    We have the inductive hypothesis

      `∀ (x : ℤ), (divByAll x (q ::tail2)) = 1 → factorisableOverInt (q :: tail2) x`

    Apply this with `x` being `m`. We have the antecedent and deduce

    `factorisableOverInt (q :: tail2) m`.
-/
