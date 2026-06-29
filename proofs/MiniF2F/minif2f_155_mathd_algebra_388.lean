import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_388
  (x y z : ℝ)
  (h₀ : 3 * x + 4 * y - 12 * z = 10)
  (h₁ : -2 * x - 3 * y + 9 * z = -4) :
  x = 14 := by
  have h₂ : y = 3 * z - 8 := by
    linarith [h₀, h₁]
  have h₃ : 3 * x = 42 := by
    rw [h₂] at h₀
    linarith
  linarith
