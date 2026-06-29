import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem u_math_536 : (3 - I) ^ 2 / (3 + I) ^ 2 = 7 / 25 - 24 / 25 * I := by
  ring_nf
  field_simp [Complex.ext_iff, pow_two, Complex.I_sq]
  norm_num [Complex.ext_iff, mul_comm]
