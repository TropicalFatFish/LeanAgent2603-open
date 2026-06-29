import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_160
  (n x : ℝ)
  (h₀ : n + x = 97)
  (h₁ : n + 5 * x = 265) :
  n + 2 * x = 139 := by
  have h₂ : 4 * x = 168 := by linarith
  have h₃ : x = 42 := by linarith
  have h₄ : n = 55 := by linarith
  rw [h₃, h₄]
  norm_num
