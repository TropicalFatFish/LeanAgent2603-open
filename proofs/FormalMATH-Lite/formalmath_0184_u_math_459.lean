import Mathlib

open Real

theorem u_math_459 (x : ℝ) : (cosh x + sinh x = exp x) ∧ (cosh x - sinh x = exp (-x)) := by
  constructor
  · exact cosh_add_sinh x
  · exact cosh_sub_sinh x
