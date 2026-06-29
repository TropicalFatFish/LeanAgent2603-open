import Mathlib

open Real Set
open scoped BigOperators

theorem u_math_269 :
  {x : ℝ | -4 < 3 * x + 2 ∧ 3 * x + 2 ≤ 18} = {x | -2 < x ∧ x ≤ 16 / 3} := by
  apply Set.ext
  intro x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h
    rcases h with ⟨h1, h2⟩
    have h3 : -2 < x := by
      linarith
    have h4 : x ≤ 16 / 3 := by
      linarith
    exact ⟨h3, h4⟩
  · intro h
    rcases h with ⟨h1, h2⟩
    have h3 : -4 < 3 * x + 2 := by
      linarith
    have h4 : 3 * x + 2 ≤ 18 := by
      linarith
    exact ⟨h3, h4⟩
