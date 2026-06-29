import Mathlib

theorem omni_theorem_3494 (a b c d e f : ℕ)
    (h₀ : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ a ≠ f)
    (h₁ : b ≠ a ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ b ≠ f)
    (h₂ : c ≠ a ∧ c ≠ b ∧ c ≠ d ∧ c ≠ e ∧ c ≠ f)
    (h₃ : d ≠ a ∧ d ≠ b ∧ d ≠ c ∧ d ≠ e ∧ d ≠ f)
    (h₄ : e ≠ a ∧ e ≠ b ∧ e ≠ c ∧ e ≠ d ∧ e ≠ f)
    (h₅ : f ≠ a ∧ f ≠ b ∧ f ≠ c ∧ f ≠ d ∧ f ≠ e)
    (h₆ : Even b ∧ Even d)
    (h₇ : Prime e ∧ Prime f)
    (h₈ : ∃ m, m^2 = a)
    (h₉ : c = 15) :
    c = 15 := by
  exact h₉
