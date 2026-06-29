import Mathlib

theorem algebra_528739 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / (a^3 + b^3 + a * b * c) + 1 / (b^3 + c^3 + a * b * c) +
    1 / (c^3 + a^3 + a * b * c) ≤ 1 / (a * b * c) := by
  have h₁ : a^3 + b^3 + a * b * c ≥ a * b * (a + b + c) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - b), sq_nonneg (a - b), ha, hb, hc]
  have h₂ : b^3 + c^3 + a * b * c ≥ b * c * (a + b + c) := by
    nlinarith [sq_nonneg (b - c), sq_nonneg (b - c), sq_nonneg (b - c), ha, hb, hc]
  have h₃ : c^3 + a^3 + a * b * c ≥ c * a * (a + b + c) := by
    nlinarith [sq_nonneg (c - a), sq_nonneg (c - a), sq_nonneg (c - a), ha, hb, hc]
  have h₄ : 1 / (a^3 + b^3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) := by
    apply one_div_le_one_div_of_le
    · positivity
    · exact h₁
  have h₅ : 1 / (b^3 + c^3 + a * b * c) ≤ 1 / (b * c * (a + b + c)) := by
    apply one_div_le_one_div_of_le
    · positivity
    · exact h₂
  have h₆ : 1 / (c^3 + a^3 + a * b * c) ≤ 1 / (c * a * (a + b + c)) := by
    apply one_div_le_one_div_of_le
    · positivity
    · exact h₃
  have h₇ : 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (c * a * (a + b + c)) = 1 / (a * b * c) := by
    field_simp
    ring
  linarith
