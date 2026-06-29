import Mathlib

theorem omni_theorem_3038 {x : ℝ} (hx : x * 8 = 26) : x = 26 / 8 := by
  calc
    x = (x * 8) / 8 := by field_simp [show (8 : ℝ) ≠ 0 by norm_num]
    _ = 26 / 8 := by rw [hx]
