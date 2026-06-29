import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_756
  (a b : ℝ)
  (h₀ : (2:ℝ)^a = 32)
  (h₁ : a^b = 125) :
  b^a = 243 := by
  have ha : a = 5 := by
    have hpow : (2 : ℝ) ^ a = (2 : ℝ) ^ (5 : ℝ) := by
      calc
        (2 : ℝ) ^ a = 32 := h₀
        _ = (2 : ℝ) ^ (5 : ℝ) := by norm_num [Real.rpow_natCast]
    exact (Real.rpow_right_inj (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)).mp hpow
  rw [ha] at h₁
  have hb : b = 3 := by
    have hpow : (5 : ℝ) ^ b = (5 : ℝ) ^ (3 : ℝ) := by
      calc
        (5 : ℝ) ^ b = 125 := h₁
        _ = (5 : ℝ) ^ (3 : ℝ) := by norm_num [Real.rpow_natCast]
    exact (Real.rpow_right_inj (by norm_num : (0 : ℝ) < 5) (by norm_num : (5 : ℝ) ≠ 1)).mp hpow
  rw [ha, hb]
  norm_num [Real.rpow_natCast]
