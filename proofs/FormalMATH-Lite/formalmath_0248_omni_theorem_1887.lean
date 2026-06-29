import Mathlib

theorem omni_theorem_1887 (h j z : ℕ)
    (h₀ : h * 2 + j * 3 + z * 6 = 800)
    (h₁ : h * 8 + j * 9 + z * 12 = 2018) :
    h + j + z = 203 := by
  omega
