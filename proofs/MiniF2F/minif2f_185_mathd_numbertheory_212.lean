import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_212 :
  (16^17 * 17^18 * 18^19) % 10 = 8 := by
  have h1 : (16^17) % 10 = 6 := by
    norm_num [Nat.pow_mod]

  have h2 : (17^18) % 10 = 9 := by
    norm_num [Nat.pow_mod]

  have h3 : (18^19) % 10 = 2 := by
    norm_num [Nat.pow_mod]

  have h4 : (16^17 * 17^18 * 18^19) % 10 = 8 := by
    rw [← Nat.mod_add_div (16^17) 10, ← Nat.mod_add_div (17^18) 10, ← Nat.mod_add_div (18^19) 10]
    simp only [h1, h2, h3]
    norm_num [Nat.mul_mod, Nat.add_mod]

  exact h4
