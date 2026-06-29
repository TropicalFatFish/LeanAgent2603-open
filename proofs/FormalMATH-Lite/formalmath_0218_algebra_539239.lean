import Mathlib

theorem algebra_539239 (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1) :
    a * b + b * c + c * a + 1 > 0 := by
  have ha' : -1 < a ∧ a < 1 := abs_lt.mp (by linarith)
  have hb' : -1 < b ∧ b < 1 := abs_lt.mp (by linarith)
  have hc' : -1 < c ∧ c < 1 := abs_lt.mp (by linarith)
  have ha₁ : 0 < 1 - a := by linarith
  have ha₂ : 0 < 1 + a := by linarith
  have hb₁ : 0 < 1 - b := by linarith
  have hb₂ : 0 < 1 + b := by linarith
  have hc₁ : 0 < 1 - c := by linarith
  have hc₂ : 0 < 1 + c := by linarith
  have h₁ : 0 < (1 - a) * (1 - b) * (1 - c) := by
    apply mul_pos
    . apply mul_pos; assumption'
    . assumption
  have h₂ : 0 < (1 + a) * (1 + b) * (1 + c) := by
    apply mul_pos
    . apply mul_pos; assumption'
    . assumption
  have : 0 < (1 - a) * (1 - b) * (1 - c) + (1 + a) * (1 + b) * (1 + c) := by
    linarith
  have h₃ : (1 - a) * (1 - b) * (1 - c) + (1 + a) * (1 + b) * (1 + c) = 2 * (1 + a * b + b * c + c * a) := by
    ring_nf
  have h₄ : 0 < 2 * (1 + a * b + b * c + c * a) := by linarith
  linarith
