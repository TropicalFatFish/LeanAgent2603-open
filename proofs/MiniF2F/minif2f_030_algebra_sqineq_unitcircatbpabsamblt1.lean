import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_sqineq_unitcircatbpabsamblt1
  (a b: ℝ)
  (h₀ : a^2 + b^2 = 1) :
  a * b + |a - b| ≤ 1 := by
  have h₁ : (1 - a * b)^2 ≥ (a - b)^2 := by
    have h₁_aux : 1 - 2 * (a * b) + (a * b)^2 ≥ a^2 - 2 * (a * b) + b^2 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a * b), sq_nonneg (a + b), h₀]
    simp [sq] at h₁_aux ⊢
    linarith
  have h₂ : 1 - a * b ≥ 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), h₀]
  have h₃ : 1 - a * b ≥ |a - b| := by
    have h₃' : |a - b| ≥ 0 := abs_nonneg _
    have h₃'' : (abs (a - b))^2 = (a - b)^2 := by simp
    have h₃''': (1 - a * b) ≥ 0 := h₂
    nlinarith [sq_sqrt (show ((a - b)^2) ≥ 0 by nlinarith), h₁, h₀]
  nlinarith
