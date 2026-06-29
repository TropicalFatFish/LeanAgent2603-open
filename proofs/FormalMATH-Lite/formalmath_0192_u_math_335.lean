import Mathlib

theorem u_math_335 (x : ℝ) (hx : x ≠ -2) :
    ((x ^ 2 - 4) / 2) / ((x + 2) / 3) = 3 / 2 * x - 3 := by
  have h : x + 2 ≠ 0 := by
    intro h'
    apply hx
    linarith
  field_simp [h, sub_ne_zero.mpr hx]
  ring
