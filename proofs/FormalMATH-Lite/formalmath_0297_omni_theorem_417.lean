import Mathlib

theorem omni_theorem_417 {x y : ℝ} (h₀ : x * y = 5) (h₁ : x ^ 2 + y ^ 2 = 21) :
    x ^ 4 + y ^ 4 = 391 := by
  have h₂ : x^4 + y^4 = (x^2 + y^2)^2 - 2*(x*y)^2 := by ring
  rw [h₂]
  rw [h₁]
  rw [h₀]
  norm_num
