import Mathlib

theorem omni_theorem_2917 (a : ℝ) (h : (1 : ℝ)^2 + a * 1 + 1 = 0) : a = -2 := by
  ring_nf at h
  linarith
