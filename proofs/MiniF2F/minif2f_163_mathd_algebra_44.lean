import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_44
  (s t : ℝ)
  (h₀ : s = 9 - 2 * t)
  (h₁ : t = 3 * s + 1) :
  s = 1 ∧ t = 4 := by
  rw [h₁] at h₀
  have h₂ : s = 1 := by linarith
  rw [h₂] at h₁
  exact ⟨h₂, by linarith⟩
