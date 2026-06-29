import Mathlib

theorem omni_theorem_1859
    (x y z : ℝ)
    (h₀ : x + 2 * y - 3 * z = 7)
    (h₁ : 2 * x - y + 2 * z = 6) :
    8 * x + y = 32 := by
  have h₂ : 2 * x + 4 * y - 6 * z = 14 := by linarith
  have h₃ : 6 * x - 3 * y + 6 * z = 18 := by linarith
  linarith
