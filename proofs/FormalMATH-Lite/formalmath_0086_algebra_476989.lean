import Mathlib

theorem algebra_476989 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b + c + d = 1) :
    2 ≤ 1 / (4 * a + 3 * b + c) + 1 / (3 * a + b + 4 * d) +
        1 / (a + 4 * c + 3 * d) + 1 / (4 * b + 3 * c + d) := by
  set p₁ := 4 * a + 3 * b + c
  set p₂ := 3 * a + b + 4 * d
  set p₃ := a + 4 * c + 3 * d
  set p₄ := 4 * b + 3 * c + d
  have h_pos₁ : 0 < p₁ := by positivity
  have h_pos₂ : 0 < p₂ := by positivity
  have h_pos₃ : 0 < p₃ := by positivity
  have h_pos₄ : 0 < p₄ := by positivity
  have h_sum : p₁ + p₂ + p₃ + p₄ = 8 := by
    ring_nf at h ⊢
    linarith
  have h_sum_inv : (1 / p₁) + (1 / p₂) + (1 / p₃) + (1 / p₄) ≥ 2 := by
    have h₁ : (p₁ + p₂ + p₃ + p₄) * ((1 / p₁) + (1 / p₂) + (1 / p₃) + (1 / p₄)) ≥ 16 := by
      have h₂ : 0 < p₁ * p₂ := mul_pos h_pos₁ h_pos₂
      have h₃ : 0 < p₃ * p₄ := mul_pos h_pos₃ h_pos₄
      have h₄ : 0 < p₁ * p₃ := mul_pos h_pos₁ h_pos₃
      have h₅ : 0 < p₁ * p₄ := mul_pos h_pos₁ h_pos₄
      have h₆ : 0 < p₂ * p₃ := mul_pos h_pos₂ h_pos₃
      have h₇ : 0 < p₂ * p₄ := mul_pos h_pos₂ h_pos₄
      field_simp [h_pos₁, h_pos₂, h_pos₃, h_pos₄]
      ring_nf
      nlinarith [sq_nonneg (p₁ - p₂), sq_nonneg (p₁ - p₃), sq_nonneg (p₁ - p₄),
        sq_nonneg (p₂ - p₃), sq_nonneg (p₂ - p₄), sq_nonneg (p₃ - p₄)]
    have h₃ : (p₁ + p₂ + p₃ + p₄) * ((1 / p₁) + (1 / p₂) + (1 / p₃) + (1 / p₄)) = 8 * ((1 / p₁) + (1 / p₂) + (1 / p₃) + (1 / p₄)) := by
      rw [h_sum]
    rw [h₃] at h₁
    linarith
  calc
    2 ≤ (1 / p₁) + (1 / p₂) + (1 / p₃) + (1 / p₄) := by linarith
    _ = 1 / (4 * a + 3 * b + c) + 1 / (3 * a + b + 4 * d) + 1 / (a + 4 * c + 3 * d) + 1 / (4 * b + 3 * c + d) := by
      simp [p₁, p₂, p₃, p₄]
