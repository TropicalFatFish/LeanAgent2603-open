import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_263
  (y : ℝ)
  (h₀ : 0 ≤ 19 + 3 * y)
  (h₁ : Real.sqrt (19 + 3 * y) = 7) :
  y = 10 := by
  have h₂ : 19 + 3 * y = 49 := by
    apply Eq.symm
    nlinarith [sq_sqrt h₀, congr_arg (λ x => x ^ 2) h₁]
  linarith
