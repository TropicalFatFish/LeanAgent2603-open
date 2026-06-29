import Mathlib

theorem algebra_403235 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    (1 + a) * (1 + b) * (1 + c) ≥ 8 * (1 - a) * (1 - b) * (1 - c) := by
  have h1 : 1 - a = b + c := by linarith
  have h2 : 1 - b = a + c := by linarith
  have h3 : 1 - c = a + b := by linarith
  have h4 : 1 + a = 2 - (b + c) := by linarith
  have h5 : 1 + b = 2 - (a + c) := by linarith
  have h6 : 1 + c = 2 - (a + b) := by linarith
  have h7 : 0 < b + c := by linarith
  have h8 : 0 < a + c := by linarith
  have h9 : 0 < a + b := by linarith
  have h10 : 0 < (b + c) * (a + c) * (a + b) := by positivity
  have h11 : 0 < a * b * c := by positivity
  have h12 : (a + b) * (b + c) * (c + a) ≥ 8 * a * b * c := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    mul_nonneg ha.le hb.le, mul_nonneg hb.le hc.le, mul_nonneg hc.le ha.le]
