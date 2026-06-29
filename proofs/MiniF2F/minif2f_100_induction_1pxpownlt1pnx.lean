import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem induction_1pxpownlt1pnx
  (x : ℝ)
  (n : ℕ)
  (h₀ : -1 < x)
  (h₁ : 0 < n) :
  (1 + ↑n*x) ≤ (1 + x)^(n:ℕ) := by
  induction' h₁ with n ih
  · norm_num
  · simp_all [pow_succ, mul_add, add_assoc]
    nlinarith [sq_nonneg x, mul_nonneg (by norm_num : (0 : ℝ) ≤ ↑n) (sq_nonneg x)]
