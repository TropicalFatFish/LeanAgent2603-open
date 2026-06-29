import Mathlib

theorem omni_theorem_2880 (x y z : ℝ) (hx : x = 3) (hy : y = 2 * x) (hz : z = 3 * y) :
    (x + y + z) / 3 = 9 := by
  rw [hx, hy, hz] at *
  norm_num [hx, hy, hz]
