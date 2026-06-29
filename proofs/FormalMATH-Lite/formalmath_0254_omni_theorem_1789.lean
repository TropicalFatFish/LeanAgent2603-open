import Mathlib

theorem omni_theorem_1789 : (1032^1032) % 100 = 76 := by
  set_option exponentiation.threshold 2000 in
  norm_num
