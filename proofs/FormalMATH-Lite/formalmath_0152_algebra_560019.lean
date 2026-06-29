import Mathlib

theorem algebra_560019 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x^2 + y^2 + z^2 = 1) :
    x^2 * y * z + y^2 * x * z + z^2 * x * y ≤ 1 / 3 := by
  ring_nf
  <;> nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
    mul_pos hx hy, mul_pos hy hz, mul_pos hz hx]
