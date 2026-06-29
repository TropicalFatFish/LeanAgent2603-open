import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem amc12b_2020_p22
  (t : ℝ) :
  ((2^t - 3 * t) * t) / (4^t) ≤ 1 / 12 := by
  have hden : 0 < (4 : ℝ) ^ t := by positivity
  have hpow : (4 : ℝ) ^ t = ((2 : ℝ) ^ t) ^ 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num]
    rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2) 2 t]
    rw [show ((2 : ℕ) : ℝ) * t = t * (2 : ℕ) by norm_num [mul_comm]]
    rw [Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2) t 2]
  have hmain : 12 * (((2 : ℝ) ^ t - 3 * t) * t) ≤ ((2 : ℝ) ^ t) ^ 2 := by
    nlinarith [sq_nonneg (((2 : ℝ) ^ t) - 6 * t)]
  rw [div_le_iff₀ hden, hpow]
  nlinarith
