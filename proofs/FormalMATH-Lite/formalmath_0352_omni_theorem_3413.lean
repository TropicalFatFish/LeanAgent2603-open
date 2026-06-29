import Mathlib

theorem omni_theorem_3413 (d : ℝ) (h : d = 312 + 858) :
    (d / 2) - 312 = 273 := by
  rw [h]
  norm_num
