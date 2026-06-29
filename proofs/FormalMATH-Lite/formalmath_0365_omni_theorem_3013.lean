import Mathlib

theorem omni_theorem_3013 (l w h : ℝ) (hw : l * w * h = 12) :
    (2 * l) * (2 * w) * (3 * h) = 144 := by
  calc
    (2 * l) * (2 * w) * (3 * h) = 12 * (l * w * h) := by ring
    _ = 12 * 12 := by simp [hw]
    _ = 144 := by norm_num
