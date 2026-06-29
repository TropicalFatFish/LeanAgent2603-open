import Mathlib

theorem u_math_219 (x y : ℝ) (t : ℝ) (h : t ≠ 0) (hx : x = 3 * t + 3 / (4 * t)) (hy : y = 5 * t - 5 / (4 * t)) : x ^ 2 / 9 - y ^ 2 / 25 = 1 := by
  rw [hx, hy]
  rw [div_eq_mul_inv]
  simp [mul_add, add_mul, pow_two]
  field_simp [h]
  ring
  <;> field_simp [h]
  <;> ring
