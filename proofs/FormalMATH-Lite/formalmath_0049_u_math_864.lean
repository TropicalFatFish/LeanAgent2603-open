import Mathlib

open Real Set
open scoped BigOperators

theorem u_math_864 : {x : ℝ | -5 * x ^ 2 + 10 * x + 15 ≤ 0} = {x | x ≤ -1 ∨ x ≥ 3} := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hx

    have h1 : -5 * (x - 3) * (x + 1) ≤ 0 := by
      nlinarith

    have h2 : (x - 3) * (x + 1) ≥ 0 := by
      nlinarith

    by_cases hx : x ≤ -1
    · exact Or.inl hx

    · have h3 : x + 1 > 0 := by linarith

      have h4 : x - 3 ≥ 0 := by
        contrapose! h2
        nlinarith
      exact Or.inr (by linarith)
  · intro hx
    cases hx with
    | inl hx =>

      nlinarith
    | inr hx =>

      nlinarith
