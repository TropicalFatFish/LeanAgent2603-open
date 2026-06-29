import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_328 :
  (5^999999) % 7 = 6 := by
  have h : 999999 % 6 = 3 := by
    norm_num
  have h2 : (5 ^ 999999) % 7 = 6 := by
    have h3 : (5 ^ 6) % 7 = 1 := by
      rfl
    have h4 : (5 ^ 999999) % 7 = (5 ^ 3) % 7 := by
      rw [← Nat.mod_add_div 999999 6, pow_add, pow_mul]
      <;> simp [h, h3, Nat.pow_mod, Nat.mul_mod, Nat.add_mod, pow_two]
      <;> norm_num
    rw [h4]
    rfl
  exact h2
