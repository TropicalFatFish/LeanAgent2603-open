import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_80
  (x : ℝ)
  (h₀ : x ≠ -1)
  (h₁ : (x - 9) / (x + 1) = 2) :
  x = -11 := by
  have h₂ : x + 1 ≠ 0 := by
    intro h
    have : x = -1 := by
      rw [add_eq_zero_iff_neg_eq] at h
      linarith
    exact h₀ this
  field_simp [h₂] at h₁
  linarith
