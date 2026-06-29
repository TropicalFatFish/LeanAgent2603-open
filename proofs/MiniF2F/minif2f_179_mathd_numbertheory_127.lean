import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_127 :
  (∑ k ∈ (Finset.range 101), 2^k) % 7 = 3 := by
  have h : 2 ^ 3 ≡ 1 [MOD 7] := by norm_num
  have : (∑ k ∈ Finset.range 101, 2 ^ k) % 7 = 3 := by
    simp [Finset.sum_range_succ, Nat.ModEq] at h
    norm_num [Finset.sum_range_succ, h]
    <;> rfl
  exact this
