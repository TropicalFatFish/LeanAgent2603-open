import Mathlib

open Real Set
open scoped Real

theorem u_math_903 {θ : ℝ} : sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2 := by
  constructor
  ·
    rw [cos_two_mul]
    have h₁ : sin θ ^ 2 = 1 - cos θ ^ 2 := by
      have := cos_sq_add_sin_sq θ
      linarith
    rw [h₁]
    ring
  ·
    rw [cos_two_mul]
    have h₁ : cos θ ^ 2 = 1 - sin θ ^ 2 := by
      have := cos_sq_add_sin_sq θ
      linarith
    rw [h₁]
    ring
