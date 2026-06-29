import Mathlib

theorem omni_theorem_373 (x : ℝ) (hx : x^3 + x^2 + x + 1 = 0) :
    x^4 + 2 * x^3 + 2 * x^2 + 2 * x + 1 = 0 := by
  have h_main : x ^ 4 + 2 * x ^ 3 + 2 * x ^ 2 + 2 * x + 1 = (x + 1) * (x ^ 3 + x ^ 2 + x + 1) := by ring
  rw [h_main]
  rw [hx]
  simp
