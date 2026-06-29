import Mathlib

open Complex

theorem u_math_758 : (3 + I) ^ 2 / (1 + 2 * I) ^ 2 = -2 * I := by
  field_simp [Complex.ext_iff, pow_two]
  ring_nf
  norm_num
  <;> simp [Complex.ext_iff, pow_two]
  <;> norm_num
  <;> ring
