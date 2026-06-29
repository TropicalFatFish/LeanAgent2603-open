import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_153
  (n : ℝ)
  (h₀ : n = 1 / 3) :
  Int.floor (10 * n) + Int.floor (100 * n) + Int.floor (1000 * n) + Int.floor (10000 * n) = 3702 := by
  rw [h₀]
  simp [Int.floor_eq_iff]
  all_goals norm_num
  <;> linarith
  <;> norm_num
