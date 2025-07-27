import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic

open Module FiniteDimensional

variable {K V : Type*}
  [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

example {ι : Type*} [Fintype ι]
    (f : ι → V) (h : Fintype.card ι > finrank K V) :
  ¬ LinearIndependent K f := by
  intro hf
  -- hf.fintype_card_le_finrank : Fintype.card ι ≤ finrank K V
  have hle := hf.fintype_card_le_finrank
  -- contradicts h : Fintype.card ι > finrank K V
  linarith

abbrev F₂ : Type := GaloisField 2 1

example {m n : ℕ} (f : Fin n → (Fin m → F₂)) (h : n > m) :
    ¬ LinearIndependent F₂ f := by
  intro hf
  have hle := hf.fintype_card_le_finrank
  simp only [Module.finrank_pi, Fintype.card_fin] at *
  linarith
