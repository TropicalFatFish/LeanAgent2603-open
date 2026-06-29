import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_320
  (x : ℝ)
  (a b c : ℕ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 ≤ x)
  (h₁ : 2 * x^2 = 4 * x + 9)
  (h₂ : x = (a + Real.sqrt b) / c)
  (h₃ : c = 2) :
  a + b + c = 26 := by
  subst c
  have hx_lt4 : x < 4 := by
    nlinarith [sq_nonneg (x - 4)]
  have hs_ge_one : 1 ≤ Real.sqrt (b : ℝ) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast h₀.2.1
  have ha_lt7 : a < 7 := by
    have hreal : (a : ℝ) < 7 := by
      nlinarith [h₂, hs_ge_one, hx_lt4]
    exact_mod_cast hreal
  have hs_lt8 : Real.sqrt (b : ℝ) < 8 := by
    have ha_nonneg : 0 ≤ (a : ℝ) := by positivity
    nlinarith [h₂, ha_nonneg, hx_lt4]
  have hb_lt64 : b < 64 := by
    have hreal : (b : ℝ) < 64 := by
      have hsq := (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 8)).mp hs_lt8
      nlinarith [hsq]
    exact_mod_cast hreal
  have hs_sq : (Real.sqrt (b : ℝ)) ^ 2 = b := Real.sq_sqrt (by positivity)
  have hlin : (2 * (a : ℝ) - 4) * Real.sqrt (b : ℝ) = 4 * (a : ℝ) + 18 - (a : ℝ)^2 - (b : ℝ) := by
    nlinarith [h₁, h₂, hs_sq]
  have hpoly : ((2 * (a : ℝ) - 4)^2) * (b : ℝ) = (4 * (a : ℝ) + 18 - (a : ℝ)^2 - (b : ℝ))^2 := by
    calc
      ((2 * (a : ℝ) - 4)^2) * (b : ℝ) = ((2 * (a : ℝ) - 4) * Real.sqrt (b : ℝ))^2 := by
        rw [mul_pow, hs_sq]
      _ = (4 * (a : ℝ) + 18 - (a : ℝ)^2 - (b : ℝ))^2 := by
        rw [hlin]
  interval_cases a <;> interval_cases b <;> norm_num at hpoly
  all_goals norm_num
