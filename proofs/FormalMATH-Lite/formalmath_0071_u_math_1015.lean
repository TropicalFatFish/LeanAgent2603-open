import Mathlib

open Real

theorem u_math_1015 : log (6 / sqrt (exp 3)) = log 6 - 3 / 2 := by
  rw [Real.log_div (by norm_num) (by positivity)]
  rw [Real.log_sqrt (by positivity)]
  rw [Real.log_exp 3]
  <;> norm_num
