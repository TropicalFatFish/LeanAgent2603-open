import Mathlib

theorem u_math_513 {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t) :
    P (-530 / 21) = 0 ∧ P 0 = 53000 := by
  rw [hP]
  constructor
  · norm_num [mul_comm]
  · norm_num
