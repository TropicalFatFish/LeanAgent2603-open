import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_343 :
  (∏ k ∈ Finset.range 6, (2 * k + 1)) % 10 = 5 := by
  simp [Finset.prod_range_succ, mul_add, add_mul, mul_one, mul_comm, mul_left_comm, mul_assoc]
  <;> norm_num
  <;> rfl
