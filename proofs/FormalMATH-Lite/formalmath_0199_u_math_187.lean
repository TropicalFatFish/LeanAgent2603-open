import Mathlib

open Real

theorem u_math_187 (x : ℝ) : 2 * ((sin x)^6 + (cos x)^6) - 3 * ((sin x)^4 + (cos x)^4) = -1 := by
  have h1 : (sin x)^2 + (cos x)^2 = 1 := by
    rw [Real.sin_sq_add_cos_sq]
  ring_nf at *
  simp [h1, sq, mul_assoc, mul_comm, mul_left_comm] at *
  nlinarith [sq_nonneg ((sin x)^2 - (cos x)^2), sq_nonneg ((sin x)^2 + (cos x)^2)]
