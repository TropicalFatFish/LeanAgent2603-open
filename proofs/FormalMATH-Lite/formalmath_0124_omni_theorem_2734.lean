import Mathlib

theorem omni_theorem_2734 (a b c d e : ℝ)
    (h₀ : (a + b + c) / 3 = 16) (h₁ : (c + d + e) / 3 = 26)
    (h₂ : (a + b + c + d + e) / 5 = 20) :
    c = 26 := by
  have h₃ : a + b + c = 48 := by
    have h₃₁ : (a + b + c) / 3 * 3 = 16 * 3 := by rw [h₀]
    simp at h₃₁
    linarith

  have h₄ : a + b + c + d + e = 100 := by
    have h₄₁ : (a + b + c + d + e) / 5 * 5 = 20 * 5 := by rw [h₂]
    simp at h₄₁
    linarith

  have h₅ : c + d + e = 78 := by
    have h₅₁ : (c + d + e) / 3 * 3 = 26 * 3 := by rw [h₁]
    simp at h₅₁
    linarith

  have h₆ : d + e = 52 := by linarith

  linarith
