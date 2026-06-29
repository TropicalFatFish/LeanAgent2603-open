import Mathlib

theorem omni_theorem_2799 (n : ℤ) (h : 3 * n = 6 * 2) : n = 4 := by
  norm_num at h ⊢
  linarith
