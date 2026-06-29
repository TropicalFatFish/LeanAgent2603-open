import Mathlib

theorem omni_theorem_726 {P : Polynomial ℝ} (hP : ∀ x, P.eval x = P.eval 0 + P.eval 1 * x + P.eval 2 * x ^ 2)
    (hP' : P.eval (-1) = 1) : P.eval 3 = 5 := by
  have := hP 0
  have := hP 1
  have := hP 2
  have := hP (-1)
  have := hP 3
  simp at *
  ring_nf at *
  linarith
