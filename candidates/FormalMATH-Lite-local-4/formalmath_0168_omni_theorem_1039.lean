import Mathlib

open Finset Real Nat

def b : ℕ → ℝ
| j => (j ^ 2014) * ∏ i ∈ Icc 1 2014 \ {j}, ((i ^ 2014 - j ^ 2014))

theorem omni_theorem_1039 : ∑ j ∈ Icc 1 2014, (1 / b j) = 1 / (Nat.factorial 2014) ^ 2014 := by

  refine Nat.choose_eq_factorial_mul.inv (Nat.choose_eq_factorial_mul.zero).symm rfl

  <;> simp [b, Icc, Finset.prod, Finset.filter]
  <;> rfl
