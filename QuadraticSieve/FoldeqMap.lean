import Mathlib

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
