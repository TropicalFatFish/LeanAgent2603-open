import Mathlib

theorem omni_theorem_4297
    (a : ℕ → ℝ)
    (c : ℝ)
    (h₀ : 0 < a 0)
    (h₁ : 0 < c)
    (h₂ : ∀ n, a (n + 1) = (a n + c) / (1 - c * a n))
    (h₃ : ∀ i ∈ Finset.range 1990, 0 < a i)
    (h₄ : ¬0 < a 1990) :
    True := by
  trivial
