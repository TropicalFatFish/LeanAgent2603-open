import Mathlib

theorem omni_theorem_2816 (x : ℝ) (hx : x ≠ 0) (h : (x / 100) * 60 = 12) :
    (15 / 100) * x = 3 := by
  have h' : x = 20 := by
    field_simp at h
    linarith
  rw [h']
  field_simp
  linarith
