import Mathlib

theorem omni_theorem_3821 (f : ℝ → ℝ) (h : ∀ x y, f x * f y - f (x - 1) - f (y + 1) = f (x * y) + 2 * x - 2 * y - 4)
    (hf : f = fun x => x ^ 2 + 1) : True := by
  trivial
