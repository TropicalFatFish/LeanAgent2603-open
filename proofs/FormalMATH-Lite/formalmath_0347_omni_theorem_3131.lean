import Mathlib

theorem omni_theorem_3131 {x y : ℝ} (hx : x = 320 * 0.8) (hy : y = 80 * 0.9) :
    (320 + 80 - (x + y)) / (320 + 80) * 100 = 18 := by
  rw [hx, hy]
  norm_num
