import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_246
  (a b : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = a * x^4 - b * x^2 + x + 5)
  (h₂ : f (-3) = 2) :
  f 3 = 8 := by
  have h₃ : a * (-3)^4 - b * (-3)^2 + (-3) + 5 = 2 := by
    rw [h₀] at h₂
    exact h₂

  have h₄ : 81 * a - 9 * b = 0 := by
    simp only [pow_succ] at h₃
    ring_nf at h₃ ⊢
    linarith

  rw [h₀]
  norm_num at *
  ring_nf
  linarith
