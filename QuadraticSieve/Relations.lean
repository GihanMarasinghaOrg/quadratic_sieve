import Mathlib.LinearAlgebra.LinearIndependent.Basic

variable {R : Type*} [Field R]
variable {V : Type*} [AddCommGroup V] [Module ℤ V]

open Set Finset

def ι := Fin 3

def f : ι → V := fun _ => 0

example : ¬LinearIndependent ℤ (f : ι → V) := by
  intro hf
  set g : ι →₀ ℤ := Finsupp.single ⟨0, by decide⟩ 1 with b
  have gzero : Finsupp.linearCombination ℤ f g = (0 : V) := by
    simp [Finsupp.linearCombination, f, g]
  have g_ne_zero : g ≠ 0 := by
    intro h
    have h₁ : g ⟨0, by decide⟩ = 0 := by rw [h]; rfl
    have h₂ : (0 : ℤ) = 1 := by rw [←h₁, b]; simp
    contradiction
  specialize @hf g 0
  apply g_ne_zero
  apply hf
  rw [gzero, map_zero]
