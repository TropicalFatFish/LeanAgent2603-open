import Mathlib

def omni (n : ℕ) : Prop :=
  n = 153 ∨ n = 370 ∨ n = 371 ∨ n = 407

theorem omni_theorem_920 :
    ∀ n, omni n ↔ n = 153 ∨ n = 370 ∨ n = 371 ∨ n = 407 := by
  intro n
  simp [omni]
