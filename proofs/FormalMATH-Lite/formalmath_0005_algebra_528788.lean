import Mathlib

theorem algebra_528788 (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1) :
    a * b + b * c + c * a + 1 > 0 := by
  have ha' : a * a < 1 := by
    cases' abs_cases a with ha' ha' <;> nlinarith [ha]
  have hb' : b * b < 1 := by
    cases' abs_cases b with hb' hb' <;> nlinarith [hb]
  have hc' : c * c < 1 := by
    cases' abs_cases c with hc' hc' <;> nlinarith [hc]
  nlinarith [sq_nonneg (a + b + c),
    sq_nonneg (a + b),
    sq_nonneg (b + c),
    sq_nonneg (c + a),
    sq_nonneg (a - b),
    sq_nonneg (b - c),
    sq_nonneg (c - a),
    ha', hb', hc']
