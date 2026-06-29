import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_156
  (x y : ℝ)
  (f g : ℝ → ℝ)
  (h₀ : ∀t, f t = t^4)
  (h₁ : ∀t, g t = 5 * t^2 - 6)
  (h₂ : f x = g x)
  (h₃ : f y = g y)
  (h₄ : x^2 < y^2) :
  y^2 - x^2 = 1 := by
  have h₅ : x^4 - 5 * x^2 + 6 = 0 := by
    rw [h₀, h₁] at h₂
    linarith

  have h₆ : y^4 - 5 * y^2 + 6 = 0 := by
    rw [h₀, h₁] at h₃
    linarith

  have hx : x^2 = 2 ∨ x^2 = 3 := by
    have hx₁ : (x^2 - 2) * (x^2 - 3) = 0 := by
      linarith
    have hx₂ : x^2 - 2 = 0 ∨ x^2 - 3 = 0 := by
      apply eq_zero_or_eq_zero_of_mul_eq_zero hx₁
    cases hx₂ with
    | inl hx₂ =>
      have hx₃ : x^2 = 2 := by linarith
      exact Or.inl hx₃
    | inr hx₂ =>
      have hx₃ : x^2 = 3 := by linarith
      exact Or.inr hx₃

  have hy : y^2 = 2 ∨ y^2 = 3 := by
    have hy₁ : (y^2 - 2) * (y^2 - 3) = 0 := by
      linarith
    have hy₂ : y^2 - 2 = 0 ∨ y^2 - 3 = 0 := by
      apply eq_zero_or_eq_zero_of_mul_eq_zero hy₁
    cases hy₂ with
    | inl hy₂ =>
      have hy₃ : y^2 = 2 := by linarith
      exact Or.inl hy₃
    | inr hy₂ =>
      have hy₃ : y^2 = 3 := by linarith
      exact Or.inr hy₃

  have h₇ : x^2 = 2 ∧ y^2 = 3 := by
    cases hx with
    | inl hx =>
      cases hy with
      | inl hy =>
        have h₈ : x^2 = 2 := hx
        have h₉ : y^2 = 2 := hy
        have h₁₀ : x^2 < y^2 := h₄
        linarith
      | inr hy =>
        exact ⟨hx, hy⟩
    | inr hx =>
      cases hy with
      | inl hy =>
        have h₈ : x^2 = 3 := hx
        have h₉ : y^2 = 2 := hy
        have h₁₀ : x^2 < y^2 := h₄
        linarith
      | inr hy =>
        exfalso
        have h₈ : x^2 = 3 := hx
        have h₉ : y^2 = 3 := hy
        have h₁₀ : x^2 < y^2 := h₄
        linarith

  cases h₇ with
  | intro hx hy =>
    simp at *
    linarith
