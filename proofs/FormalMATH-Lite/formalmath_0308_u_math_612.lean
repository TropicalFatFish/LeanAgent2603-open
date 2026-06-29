import Mathlib

theorem u_math_612 (x y : ℝ) (hx : x < y) (hy : y < 0) :
    Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x := by
  have hxy : x - y < 0 := by linarith
  have hxy2 : x + y < 0 := by linarith
  rw [Real.sqrt_sq_eq_abs (x - y), Real.sqrt_sq_eq_abs (x + y)]
  simp [abs_of_neg hxy, abs_of_neg hxy2]
  ring
