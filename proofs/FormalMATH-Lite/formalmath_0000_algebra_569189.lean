import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_569189 (x : ℝ) :
  |sqrt (x^2 + x + 1) - sqrt (x^2 - x + 1)| < 1 := by
  set a : ℝ := x ^ 2 + x + 1 with a_def
  set b : ℝ := x ^ 2 - x + 1 with b_def
  have ha : 0 ≤ a := by
    rw [a_def]
    nlinarith [sq_nonneg (x + (1 / 2 : ℝ))]
  have hb : 0 ≤ b := by
    rw [b_def]
    nlinarith [sq_nonneg (x - (1 / 2 : ℝ))]
  have hx_to_b : x - (1 / 2 : ℝ) < sqrt b := by
    apply Real.lt_sqrt_of_sq_lt
    rw [b_def]
    nlinarith
  have hnx_to_a : -x - (1 / 2 : ℝ) < sqrt a := by
    apply Real.lt_sqrt_of_sq_lt
    rw [a_def]
    nlinarith
  rw [abs_lt]
  constructor
  · have hpos : 0 < sqrt a + 1 := by positivity
    have hb_lt : sqrt b < sqrt a + 1 := by
      rw [Real.sqrt_lt' hpos]
      nlinarith [Real.sq_sqrt ha, a_def, b_def, hnx_to_a]
    linarith
  · have hpos : 0 < sqrt b + 1 := by positivity
    have ha_lt : sqrt a < sqrt b + 1 := by
      rw [Real.sqrt_lt' hpos]
      nlinarith [Real.sq_sqrt hb, a_def, b_def, hx_to_b]
    linarith
