import Mathlib

open Finset Real

theorem omni_theorem_1386 : ∏ i ∈ Icc 2 6, ((i^3 - 1) / (i^3 + 1)) = 43 / 63 := by
  norm_num [mul_comm, mul_assoc, mul_left_comm, Finset.prod_Icc_succ_top]
