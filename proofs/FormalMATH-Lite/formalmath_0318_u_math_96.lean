import Mathlib

theorem u_math_96 (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50) :
    x ≤ 110 := by
  linarith
