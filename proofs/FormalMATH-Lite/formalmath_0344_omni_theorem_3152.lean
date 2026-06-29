import Mathlib

theorem omni_theorem_3152 (l : ℝ) (hl : l = 1 / 2) (d : ℝ) (hd : d = 12) :
    d / l = 24 := by
  rw [hd, hl]
  <;> norm_num
