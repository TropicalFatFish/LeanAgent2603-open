import Mathlib

theorem theorem_proving_zh_blue_856 (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ)
    (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2))
    (hx₁ : x₁ > 0) (hx₂ : x₂ < 0) :
    x₁ < 1 ∧ x₂ > -1 := by
  have h_disc : a ^ 2 > 1 := by nlinarith
  have h₃ : 2 * a ^ 2 * x₁ ^ 2 + 2 * a * x₁ + 1 - a ^ 2 = 0 := by
    nlinarith
  have h₄ : 2 * a ^ 2 * x₂ ^ 2 + 2 * a * x₂ + 1 - a ^ 2 = 0 := by
    nlinarith

  have h₅ : (a + 1) ^ 2 > 0 := by nlinarith
  have : 2 * a ^ 2 * 1 ^ 2 + 2 * a * 1 + 1 - a ^ 2 > 0 := by nlinarith
  have h₆ : x₁ < 1 := by
    nlinarith [sq_nonneg (x₁ - 1)]

  have : 2 * a ^ 2 * (-1) ^ 2 + 2 * a * (-1) + 1 - a ^ 2 > 0 := by nlinarith
  have h₇ : x₂ > -1 := by
    nlinarith [sq_nonneg (x₂ + 1)]
  exact ⟨h₆, h₇⟩
