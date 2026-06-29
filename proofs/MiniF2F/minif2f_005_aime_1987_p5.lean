import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1987_p5
  (x y : ℤ)
  (h₀ : y^2 + 3 * (x^2 * y^2) = 30 * x^2 + 517):
  3 * (x^2 * y^2) = 588 := by
  have hx2_nonneg : 0 ≤ x ^ 2 := sq_nonneg x
  have hy2_nonneg : 0 ≤ y ^ 2 := sq_nonneg y
  have hy_bound : y ^ 2 ≤ 517 := by
    by_cases hY : 10 ≤ y ^ 2
    · have hleft : 30 * x ^ 2 ≤ 3 * (x ^ 2 * y ^ 2) := by
        nlinarith
      nlinarith
    · nlinarith
  have hy_low : -22 ≤ y := by
    nlinarith [sq_nonneg (y + 23)]
  have hy_high : y ≤ 22 := by
    nlinarith [sq_nonneg (y - 23)]
  interval_cases y <;>
    (have hx_bound : x ^ 2 ≤ 517 := by nlinarith [sq_nonneg x]
     have hx_low : -23 ≤ x := by nlinarith [sq_nonneg (x + 24)]
     have hx_high : x ≤ 23 := by nlinarith [sq_nonneg (x - 24)]
     interval_cases x <;> norm_num at h₀
     all_goals norm_num
     all_goals nlinarith)
