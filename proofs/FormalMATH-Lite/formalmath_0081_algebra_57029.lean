import Mathlib

theorem algebra_57029 (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i) :
    x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) := by
  ring_nf at *
  have h1 : 0 < x 0 := hx 0
  have h2 : 0 < x 1 := hx 1
  have h3 : 0 < x 2 := hx 2
  nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0 - x 2), sq_nonneg (x 1 - x 2),
    sq_nonneg (x 0 + x 1 - x 2), sq_nonneg (x 0 + x 2 - x 1),
    mul_pos h1 h2, mul_pos h1 h3, mul_pos h2 h3]
