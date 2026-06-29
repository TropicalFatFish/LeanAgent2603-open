import Mathlib

open Real

theorem u_math_987 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    log (x^4 * y) = 4 * log x + log y := by
  have h1 : log (x^4 * y) = log (x^4) + log y := log_mul (ne_of_gt (pow_pos hx 4)) (ne_of_gt hy)
  have h2 : log (x^4) = 4 * log x := by
    rw [log_pow]
    <;> ring_nf
  rw [h1, h2]
