import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_346
  (f g : ℝ → ℝ)
  (h₀ : ∀ x, f x = 2 * x - 3)
  (h₁ : ∀ x, g x = x + 1) :
  g (f 5 - 1) = 7 := by
  rw [h₁]
  have h₂ : f 5 = 2 * 5 - 3 := h₀ 5
  rw [h₂]
  norm_num
