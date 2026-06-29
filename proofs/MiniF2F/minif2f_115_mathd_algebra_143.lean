import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_143
  (f g : ℝ → ℝ)
  (h₀ : ∀ x, f x = x + 1)
  (h₁ : ∀ x, g x = x^2 + 3) :
  f (g 2) = 8 := by
  have h₂ : g 2 = 7 := by
    rw [h₁ 2]
    norm_num
  rw [h₀, h₂]
  norm_num
