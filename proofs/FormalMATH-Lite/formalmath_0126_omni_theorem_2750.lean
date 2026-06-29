import Mathlib

theorem omni_theorem_2750 (x y : ℝ) (h : x + 2 * y = 30) :
    x / 5 + 2 * y / 3 + 2 * y / 5 + x / 3 = 16 := by
  have h1 : x / 5 + 2 * y / 3 + 2 * y / 5 + x / 3 = 8 * (x + 2 * y) / 15 := by
    ring
  rw [h1]
  rw [h]
  norm_num
