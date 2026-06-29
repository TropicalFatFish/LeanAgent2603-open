import Mathlib

theorem omni_theorem_2849 {x y : ℝ} (hxy : x = 2 * y ∧ y ≠ 0) : (x + 2 * y) - (2 * x + y) = -y := by
  rw [hxy.1]
  ring
