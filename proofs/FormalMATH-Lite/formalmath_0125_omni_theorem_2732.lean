import Mathlib

theorem omni_theorem_2732 (x : ℝ) (h : ∃ d, 2 * x - 3 = 4 * x + d ∧ 4 * x - 3 = 2 * x - 3 + d) :
    x = -3 / 4 := by
  rcases h with ⟨d, h1, h2⟩
  have h3 : d = -2 * x - 3 := by linarith [h1]
  have h4 : d = 2 * x := by linarith [h2]
  have h5 : -2 * x - 3 = 2 * x := by linarith
  linarith
