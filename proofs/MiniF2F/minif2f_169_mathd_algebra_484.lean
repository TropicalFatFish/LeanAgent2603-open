import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_484 :
  Real.log 27 / Real.log 3 = 3 := by
  rw [show (27 : ℝ) = 3 ^ 3 by norm_num]
  rw [Real.log_pow]
  field_simp [show (3 : ℝ) > 0 by norm_num]
  norm_num
