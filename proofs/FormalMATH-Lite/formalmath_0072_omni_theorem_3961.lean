import Mathlib

theorem omni_theorem_3961 {a b c : ℝ} (h₀ : a^2 + b = c^2) (h₁ : b^2 + c = a^2) (h₂ : c^2 + a = b^2) :
    a * b * c = 0 := by
  have h_sum : a + b + c = 0 := by
    have h₃ : a^2 + b + b^2 + c + c^2 + a = c^2 + a^2 + b^2 := by
      linarith [h₀, h₁, h₂]
    linarith [h₃]
  have : a * b * c = 0 := by
    nlinarith [h₀, h₁, h₂, h_sum, sq_nonneg (a + b + c), sq_nonneg (a + b), sq_nonneg (b + c), sq_nonneg (c + a)]
  exact this
