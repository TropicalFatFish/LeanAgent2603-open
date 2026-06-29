import Mathlib

theorem omni_theorem_3079 : (4^127 + 5^129 + 7^131) % 100 = 52 := by
  norm_num [pow_succ, Nat.mul_mod, Nat.add_mod, Nat.mod_eq_of_lt]
