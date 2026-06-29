import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_33
  (x y z : ℝ)
  (h₀ : x ≠ 0)
  (h₁ : 2 * x = 5 * y)
  (h₂ : 7 * y = 10 * z) :
  z / x = 7 / 25 := by
  have h₃ : y = 2 * x / 5 := by
    have h₃' : 5 * y = 2 * x := by linarith
    field_simp at h₃' ⊢
    linarith
  have h₄ : z = 7 * y / 10 := by
    have h₄' : 10 * z = 7 * y := by linarith
    field_simp at h₄' ⊢
    linarith
  calc
    z / x = (7 * y / 10) / x := by rw [h₄]
    _ = 7 * y / (10 * x) := by ring
    _ = 7 * (2 * x / 5) / (10 * x) := by rw [h₃]
    _ = 14 * x / (50 * x) := by ring
    _ = 7 / 25 := by
      field_simp [h₀]
      ring
