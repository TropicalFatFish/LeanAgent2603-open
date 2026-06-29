import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_114
  (a : ℝ)
  (h₀ : a = 8) :
  (16 * (a^2) ^ (1 / 3 : ℝ)) ^ (1 / 3 : ℝ) = 4 := by
  rw [h₀]
  rw [show (8^2 : ℝ) ^ (1 / 3 : ℝ) = 4 by norm_num]
  norm_num
