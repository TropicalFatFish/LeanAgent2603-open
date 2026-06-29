import Mathlib

theorem u_math_860 : Complex.I^15 = -Complex.I := by
  simp [pow_succ, Complex.I_sq]
  <;> norm_num
