import Mathlib

theorem algebra_564777 (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1)
    (hc : c ∈ Set.Ioo (-2) 1) : a * b * c > a + b + c - 2 := by
  have ha₁ : -2 < a := ha.1
  have ha₂ : a < 1 := ha.2
  have hb₁ : -2 < b := hb.1
  have hb₂ : b < 1 := hb.2
  have hc₁ : -2 < c := hc.1
  have hc₂ : c < 1 := hc.2
  have h₁ : 1 - a > 0 := by linarith
  have h₂ : 1 - b > 0 := by linarith
  have h₃ : 1 - c > 0 := by linarith
  have h₄ : a + 2 > 0 := by linarith
  have h₅ : b + 2 > 0 := by linarith
  have h₆ : c + 2 > 0 := by linarith

  have h_product : (1 - a) * (1 - b) * (1 - c) * (a + 2) * (b + 2) * (c + 2) > 0 := by
    have : (1 - a) > 0 := h₁
    have : (1 - b) > 0 := h₂
    have : (1 - c) > 0 := h₃
    have : (a + 2) > 0 := h₄
    have : (b + 2) > 0 := h₅
    have : (c + 2) > 0 := h₆
    positivity

  have h_main : a * b * c > a + b + c - 2 := by
    nlinarith
      [ha₁, ha₂, hb₁, hb₂, hc₁, hc₂, h₁, h₂, h₃, h₄, h₅, h₆,
       mul_pos h₁ h₂, mul_pos h₂ h₃, mul_pos h₃ h₁,
       mul_pos h₄ h₅, mul_pos h₅ h₆, mul_pos h₆ h₄]

  linarith [h_main]
