import Mathlib

open Real

def reflect (f : ℝ → ℝ) : ℝ → ℝ := fun x => f (-x)

def line : ℝ → ℝ := fun x => 3 * x + 6

theorem omni_theorem_2797 : (reflect line) 2 = 0 := by
  simp [reflect, line]
  norm_num
