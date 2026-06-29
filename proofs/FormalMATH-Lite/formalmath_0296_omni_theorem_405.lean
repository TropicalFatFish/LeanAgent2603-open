import Mathlib

open Real

theorem omni_theorem_405 {x y : ℝ} (hx : x = 2001^1002 - 2001^(-1002 : ℤ)) (hy : y = 2001^1002 + 2001^(-1002 : ℤ)) : x^2 - y^2 = -4 := by
  rw [hx, hy]
  <;> norm_num
  ring
  <;> simp
  <;> field_simp
  <;> norm_num
