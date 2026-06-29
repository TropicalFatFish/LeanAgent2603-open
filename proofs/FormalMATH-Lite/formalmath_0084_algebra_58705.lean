import Mathlib

theorem algebra_58705 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    9 / (a + b + c) ≤ 2 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) := by
  have h1 : 0 < a + b + c := by linarith
  have h2 : 0 < a + b := by linarith
  have h3 : 0 < b + c := by linarith
  have h4 : 0 < c + a := by linarith
  have h5 : 0 < (a + b) * (b + c) * (c + a) := by positivity
  field_simp [h1.ne', h2.ne', h3.ne', h4.ne']
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    mul_pos ha hb, mul_pos hb hc, mul_pos hc ha,
    h2, h3, h4, h5]
