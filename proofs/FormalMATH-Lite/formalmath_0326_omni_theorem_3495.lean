import Mathlib

theorem omni_theorem_3495 (l w : ℕ) (hl : l = 13) (hw : w = 10) :
    (l + 2) * (w + 2) - l * w = 50 := by
  subst hl
  subst hw
  norm_num
