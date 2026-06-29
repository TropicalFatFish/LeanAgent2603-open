import Mathlib

theorem omni_theorem_3113 {a b c : ℤ} (h₀ : a + 5 = b) (h₁ : 5 + b = c) (h₂ : b + c = a) :
    b = -10 := by
  linarith
