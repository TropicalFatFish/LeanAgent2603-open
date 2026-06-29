import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_513
  (a b : ℝ)
  (h₀ : 3 * a + 2 * b = 5)
  (h₁ : a + b = 2) :
  a = 1 ∧ b = 1 := by
  have h₂ : a + a + b = 3 := by linarith
  have h₃ : a + 2 * b = 3 := by linarith
  have h₄ : a = 1 := by linarith
  have h₅ : b = 1 := by linarith
  exact ⟨h₄, h₅⟩
