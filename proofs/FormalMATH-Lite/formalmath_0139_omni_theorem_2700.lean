import Mathlib

theorem omni_theorem_2700 (x y z : ℤ) (hx : x = 3) (hy : y = 2 * x) (hz : z = 3 * y) : z = 18 := by
  rw [hz, hy, hx]
  norm_num
