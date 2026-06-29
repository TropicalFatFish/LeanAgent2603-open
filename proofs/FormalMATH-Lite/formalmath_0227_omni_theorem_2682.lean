import Mathlib

theorem omni_theorem_2682 {a b : ℝ} (h : ∀ x, a * (x + b) = 3 * x + 12) : a + b = 7 := by
  have h0 : a * b = 12 := by
    have h₀ := h 0
    norm_num at h₀ ⊢
    linarith
  have h1 : a = 3 := by
    have h₁ := h 1
    norm_num at h₁ ⊢
    nlinarith
  have h2 : b = 4 := by
    have h₂ := h 1
    norm_num at h₂ ⊢
    nlinarith
  linarith
