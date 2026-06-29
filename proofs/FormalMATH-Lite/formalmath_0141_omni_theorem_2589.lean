import Mathlib

theorem omni_theorem_2589 (x y z : ℝ)
    (h₀ : 2 * x + y + 4 * x * y + 6 * x * z = -6)
    (h₁ : y + 2 * z + 2 * x * y + 6 * y * z = 4)
    (h₂ : x - z + 2 * x * z - 4 * y * z = -3) :
    x ^ 2 + y ^ 2 + z ^ 2 = 29 := by
  nlinarith [h₀, h₁, h₂, mul_self_nonneg (x - 1), mul_self_nonneg (y - 2), mul_self_nonneg (z + 3)]
