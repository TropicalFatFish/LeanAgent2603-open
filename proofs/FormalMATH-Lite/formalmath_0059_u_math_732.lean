import Mathlib

open Real

noncomputable def f (x : ℝ) := 9 / 5 * x + 32

noncomputable def g (x : ℝ) := 5 / 9 * (x - 32)

theorem u_math_732 : Function.LeftInverse g f := by
  intro x
  simp only [f, g]
  field_simp
  ring
