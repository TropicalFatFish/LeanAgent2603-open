import Mathlib

open Real

theorem u_math_33 : cos (2 * arctan (-7)) = -24 / 25 := by
  have h : cos (arctan (-7)) = 1 / Real.sqrt (1 + (-7 : ℝ) ^ 2) := by
    rw [cos_arctan] at *
  rw [cos_two_mul, h]
  field_simp
  <;> ring_nf
  <;> norm_num
