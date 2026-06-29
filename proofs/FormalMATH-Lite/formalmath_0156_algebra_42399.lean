import Mathlib

theorem algebra_42399 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : (1 + a) * (1 + b) * (1 + c) = 8) : a * b * c ≤ 1 := by
  have h1 : a * b + b * c + c * a + a * b * c = 7 - (a + b + c) := by
    ring_nf at h ⊢
    linarith
  have h2 : a + b + c ≥ 3 := by
    nlinarith [sq_nonneg (a + b + c - 3),
      mul_nonneg (le_of_lt ha) (le_of_lt hb),
      mul_nonneg (le_of_lt hb) (le_of_lt hc),
      mul_nonneg (le_of_lt hc) (le_of_lt ha),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    mul_nonneg (le_of_lt ha) (le_of_lt hb),
    mul_nonneg (le_of_lt hb) (le_of_lt hc),
    mul_nonneg (le_of_lt hc) (le_of_lt ha)]
