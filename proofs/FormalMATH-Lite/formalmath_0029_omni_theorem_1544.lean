import Mathlib

theorem omni_theorem_1544 (x y : ℝ) (h : 8 * y ^ 4 + 4 * x ^ 2 * y ^ 2 + 4 * x * y ^ 2 + 2 * x ^ 3 + 2 * y ^ 2 + 2 * x = x ^ 2 + 1) :
    x + 2 * y ^ 2 = 1 / 2 := by
  have h_norm : 8 * y ^ 4 + 4 * x ^ 2 * y ^ 2 + 4 * x * y ^ 2 - x ^ 2 + 2 * x ^ 3 + 2 * y ^ 2 + 2 * x - 1 = 0 := by
    linarith [h]
  nlinarith [sq_nonneg (2 * y ^ 2), sq_nonneg x, sq_nonneg (x + 2 * y ^ 2 - 1 / 2), sq_nonneg (2 * x + 2 * y ^ 2 - x), sq_nonneg y, sq_nonneg (x - 1)]
