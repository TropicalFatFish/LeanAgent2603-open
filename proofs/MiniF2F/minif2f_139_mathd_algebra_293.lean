import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_293
  (x : NNReal) :
  Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = 36 * x * Real.sqrt (35 * x) := by
  have h₄ : Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = Real.sqrt (60 * 12 * 63 * x ^ 3) := by
    have h₄₁ : Real.sqrt (60 * x) * Real.sqrt (12 * x) = Real.sqrt (60 * 12 * x ^ 2) := by
      rw [← Real.sqrt_mul (by positivity)]
      ring_nf
    rw [h₄₁]
    have h₄₂ : Real.sqrt (60 * 12 * x ^ 2) * Real.sqrt (63 * x) = Real.sqrt (60 * 12 * x ^ 2 * 63 * x) := by
      rw [← Real.sqrt_mul (by positivity)]
      ring_nf
    rw [h₄₂]
    ring_nf
  rw [h₄]
  have h₅ : Real.sqrt (60 * 12 * 63 * x ^ 3) = Real.sqrt (36 ^ 2 * 35 * x ^ 3) := by
    norm_num
  rw [h₅]
  have h₉ : Real.sqrt (36 ^ 2 * 35 * x ^ 3) = 36 * x * Real.sqrt (35 * x) := by
    rw [Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)]
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    ring
  rw [h₉]
