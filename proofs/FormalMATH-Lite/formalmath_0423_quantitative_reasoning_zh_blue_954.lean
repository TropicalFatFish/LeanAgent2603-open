import Mathlib

open Real
open scoped BigOperators

theorem quantitative_reasoning_zh_blue_954
  (A B C D a b : ℝ × ℝ)
  (h₀ : A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D)
  (h₁ : B - A = a + b)
  (h₂ : C - B = -4 * a - b)
  (h₃ : D - C = -5 * a - 2 * b) :
  D - A = 2 * (C - B) := by
  rw [show D - A = (D - C) + (C - B) + (B - A) by
    rw [sub_eq_add_neg]
    ring]
  rw [h₃, h₂, h₁]
  ring
