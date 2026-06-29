import Mathlib

theorem omni_theorem_2787 {x : ℝ} (hx : x ≠ 0) (h : 1 / 9 + 1 / 18 = 1 / x) :
    x = 6 := by
  have h1 : 1 / 9 + 1 / 18 = 1 / 6 := by
    norm_num
  have h2 : 1 / x = 1 / 6 := by
    linarith
  field_simp [hx] at h2
  linarith
