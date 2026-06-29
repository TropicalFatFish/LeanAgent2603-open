import Mathlib

theorem omni_theorem_2815
    (x y : ℝ)
    (h₀ : 3 * x + 2 * y = 6)
    (h₁ : 9 * x ^ 2 + 4 * y ^ 2 = 468) :
    x * y = -36 := by
  have h₂ : (3 * x + 2 * y) ^ 2 = 36 := by
    rw [h₀]
    norm_num
  have h₃ : 9 * x ^ 2 + 12 * x * y + 4 * y ^ 2 = 36 := by
    calc
      9 * x ^ 2 + 12 * x * y + 4 * y ^ 2 = (3 * x + 2 * y) ^ 2 := by ring
      _ = 36 := h₂
  have h₄ : 12 * x * y = -432 := by
    linarith [h₁, h₃]
  linarith
