import Mathlib

theorem omni_theorem_3072 (x y : ℤ) (hx : x = 3) (hy : y = 4) : x * y - x = 9 := by
  rw [hx, hy]
  norm_num
