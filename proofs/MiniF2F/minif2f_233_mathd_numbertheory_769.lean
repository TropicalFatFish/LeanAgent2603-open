import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_769 :
  (129^34 + 96^38) % 11 = 9 := by
  have h1 : 129 % 11 = 8 := by norm_num
  have h2 : 96 % 11 = 8 := by norm_num
  simp [h1, h2, pow_mod, add_mod]
  <;> decide
