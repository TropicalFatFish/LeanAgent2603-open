import Mathlib

open Nat

theorem omni_theorem_1840 : (Nat.digits 10 (2^41)).length = 13 := by
  norm_num
