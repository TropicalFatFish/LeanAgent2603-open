import Mathlib

theorem omni_theorem_2869 (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (h1 : 10 * x + y = 75) (h2 : 10 * y + x = 57) : x + y = 12 := by
  omega
