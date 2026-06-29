import Mathlib

theorem omni_theorem_3411 (min max : ℤ) (h₀ : min = -11) (h₁ : max = 14) :
    max - min = 25 := by
  rw [h₁, h₀]
  <;> norm_num
