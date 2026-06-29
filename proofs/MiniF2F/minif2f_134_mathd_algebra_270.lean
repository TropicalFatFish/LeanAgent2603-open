import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_270
  (f : ℝ → ℝ)
  (h₀ : ∀ x, x ≠ -2 -> f x = 1 / (x + 2)) :
  f (f 1) = 3/7 := by
  have h1 : f 1 = 1/3 := by
    have this : (1 : ℝ) ≠ -2 := by norm_num
    rw [h₀ 1 this]
    norm_num
  have h2 : f (1/3) = 3/7 := by
    have this : (1/3 : ℝ) ≠ -2 := by norm_num
    rw [h₀ (1/3) this]
    norm_num
  rw [h1]
  exact h2
