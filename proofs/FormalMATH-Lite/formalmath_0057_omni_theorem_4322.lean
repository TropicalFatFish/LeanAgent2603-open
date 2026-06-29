import Mathlib

theorem omni_theorem_4322 (a b c d : ℝ)
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
    (h₁ : a + b + c + d = 48)
    (h₂ : a + 3 = b - 3)
    (h₃ : b - 3 = 3 * c)
    (h₄ : 3 * c = d / 3) :
    a = 6 ∧ b = 12 ∧ c = 3 ∧ d = 27 := by
  have h₅ : b = a + 6 := by linarith
  have h₆ : b - 3 = a + 3 := by linarith
  have h₇ : 3 * c = a + 3 := by linarith
  have h₈ : c = 1 + a / 3 := by linarith
  have h₉ : d = 3 * a + 9 := by
    linarith
  rw [h₅, h₈, h₉] at h₁
  have h₁₀ : 16 * a = 96 := by linarith
  have h₁₁ : a = 6 := by linarith
  have h₁₂ : b = 12 := by
    rw [h₅] at *
    rw [h₁₁] at *
    linarith
  have h₁₃ : c = 3 := by
    rw [h₈] at *
    rw [h₁₂] at *
    rw [h₁₁] at *
    linarith
  have h₁₄ : d = 27 := by
    rw [h₉] at *
    rw [h₁₃] at *
    rw [h₁₂] at *
    rw [h₁₁] at *
    linarith
  exact ⟨h₁₁, h₁₂, h₁₃, h₁₄⟩
