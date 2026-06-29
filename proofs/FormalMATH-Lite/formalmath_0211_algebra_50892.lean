import Mathlib

open Real Set

theorem algebra_50892 (x : ℝ) :
    arcsin x + arccos x = π / 2 := by
  rw [Real.arccos_eq_pi_div_two_sub_arcsin]
  linarith
