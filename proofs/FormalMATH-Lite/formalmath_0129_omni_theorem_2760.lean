import Mathlib

theorem omni_theorem_2760 (l w : ℝ) (hl : l = 20) (hw : w = 5) :
    (l + 10) * w - l * w = 50 := by
  rw [hl, hw]
  norm_num
