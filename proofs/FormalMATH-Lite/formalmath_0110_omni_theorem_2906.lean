import Mathlib

theorem omni_theorem_2906 (x : ℝ) (hx : x = 2) : 4 * x ^ 2 - 3 * x ^ 2 = 4 := by
  rw [hx]
  norm_num
