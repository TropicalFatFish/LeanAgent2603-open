import Mathlib

def S : Finset ℤ := {1, 2, 4, 8, 16, 20}

theorem omni_theorem_3018 (S : Finset ℤ) (hS : S = {1, 2, 4, 8, 16, 20}) :
    ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, a * b * c = 80 ∧ a + b + c = 25 := by
  rw [hS]
  refine ⟨1, by decide, 4, by decide, 20, by decide, by norm_num, by norm_num⟩
