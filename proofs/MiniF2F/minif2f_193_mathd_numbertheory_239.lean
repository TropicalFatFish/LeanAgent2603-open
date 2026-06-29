import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_239 :
  (∑ k ∈ Finset.Icc 1 12, k) % 4 = 2 := by
  norm_num [Finset.sum_Icc_succ_top]
