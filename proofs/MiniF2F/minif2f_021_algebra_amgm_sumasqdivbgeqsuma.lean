import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_amgm_sumasqdivbgeqsuma
  (a b c d : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
  a^2 / b + b^2 / c + c^2 / d + d^2 / a ≥ a + b + c + d := by
  have h₁ : a^2 / b + b ≥ 2 * a := by
    have h : 0 < b := h₀.2.1
    have h' : 0 < a := h₀.1
    have : 0 < a^2 := by positivity
    have : 0 < b := by linarith
    field_simp [h.ne']
    nlinarith [sq_nonneg (a - b)]
  have h₂ : b^2 / c + c ≥ 2 * b := by
    have h : 0 < c := h₀.2.2.1
    have h' : 0 < b := h₀.2.1
    have : 0 < b^2 := by positivity
    have : 0 < c := by linarith
    field_simp [h.ne']
    nlinarith [sq_nonneg (b - c)]
  have h₃ : c^2 / d + d ≥ 2 * c := by
    have h : 0 < d := h₀.2.2.2
    have h' : 0 < c := h₀.2.2.1
    have : 0 < c^2 := by positivity
    have : 0 < d := by linarith
    field_simp [h.ne']
    nlinarith [sq_nonneg (c - d)]
  have h₄ : d^2 / a + a ≥ 2 * d := by
    have h : 0 < a := h₀.1
    have h' : 0 < d := h₀.2.2.2
    have : 0 < d^2 := by positivity
    have : 0 < a := by linarith
    field_simp [h.ne']
    nlinarith [sq_nonneg (d - a)]
  linarith
