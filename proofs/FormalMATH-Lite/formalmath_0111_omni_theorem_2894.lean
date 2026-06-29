import Mathlib

theorem omni_theorem_2894 (x y : ℝ) (h₀ : y = 1) (h₁ : 4 * x - 2 * y + 3 = 3 * x + 3 * y) :
    x = 2 := by
  rw [h₀] at h₁
  linarith
