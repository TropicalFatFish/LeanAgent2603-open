import Mathlib

theorem u_math_537 (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710) :
    x = 12500 ∧ y = 10500 := by
  have h1 : y = 23000 - x := by linarith
  rw [h1] at hy
  have h2 : x = 12500 := by
    ring_nf at hy
    linarith
  have h3 : y = 10500 := by linarith
  exact ⟨h2, h3⟩
