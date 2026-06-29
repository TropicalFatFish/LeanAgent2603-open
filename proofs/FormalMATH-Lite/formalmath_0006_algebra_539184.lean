import Mathlib

theorem algebra_539184 {a b c : ℝ} (h : (a + c) * (a + b + c) < 0) :
    (b - c)^2 > 4 * a * (a + b + c) := by
  ring_nf
  nlinarith [sq_nonneg (b - c), sq_nonneg (b + c), sq_nonneg a, h]
