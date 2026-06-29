import Mathlib

theorem u_math_8 : ∀ x : ℝ, x ^ 2 + (2 / 3) * x - (1 / 3) = (x + (1 / 3)) ^ 2 - (4 / 9) := by
  intro x
  ring
