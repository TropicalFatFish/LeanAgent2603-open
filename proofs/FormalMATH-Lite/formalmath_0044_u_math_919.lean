import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem u_math_919 : ((2 + I) * (4 - 2 * I)) / (1 + I) = 5 - 5 * I := by
  field_simp [Complex.normSq]
  ring_nf
  norm_num [Complex.normSq, Complex.ext_iff, Complex.I_mul_I]
