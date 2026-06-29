import Mathlib

theorem algebra_52615 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z = x * y * z) :
    x^2 + y^2 + z^2 - 2 * (x * y + y * z + z * x) + 9 ≥ 0 := by
  have h1 : (x + y + z)^2 = x^2 + y^2 + z^2 + 2 * (x * y + y * z + z * x) := by
    ring
  have h2 : x^2 + y^2 + z^2 - 2 * (x * y + y * z + z * x) + 9 =
      (x + y + z)^2 - 4 * (x * y + y * z + z * x) + 9 := by
    linarith
  rw [h2]
  have h3 : (x + y + z)^2 - 4 * (x * y + y * z + z * x) + 9 ≥ 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1),
      sq_nonneg (x + y - z), sq_nonneg (y + z - x), sq_nonneg (z + x - y),
      sq_nonneg (x + y + z - 3 * Real.sqrt 3),
      mul_pos hx hy, mul_pos hy hz, mul_pos hz hx]
  linarith
