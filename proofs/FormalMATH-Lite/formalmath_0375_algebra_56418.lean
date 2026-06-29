import Mathlib

theorem algebra_56418 (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1) :
    (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6 := by
  have h_sq_sum : a^2 + b^2 + c^2 + d^2 = 1 := h
  have h_nonneg : 0 ≤ a^4 + b^4 + c^4 + d^4 := by positivity
  ring_nf at *
  nlinarith [sq_nonneg (a^2 - 1/3), sq_nonneg (b^2 - 1/3), sq_nonneg (c^2 - 1/3), sq_nonneg (d^2 - 1/3),
    sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]
