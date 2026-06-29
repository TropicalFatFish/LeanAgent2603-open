import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem imo_1964_p2
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : c < a + b)
  (h₂ : b < a + c)
  (h₃ : a < b + c) :
  a^2 * (b + c - a) + b^2 * (c + a - b) + c^2 * (a + b - c) ≤ 3 * a * b * c := by
  have h₁ : a > 0 := h₀.1
  have h₂ : b > 0 := h₀.2.1
  have h₃ : c > 0 := h₀.2.2
  have h₄ : a + b > c := by linarith
  have h₅ : b + c > a := by linarith
  have h₆ : c + a > b := by linarith
  have h₇ : 0 < a * b := mul_pos h₁ h₂
  have h₈ : 0 < b * c := mul_pos h₂ h₃
  have h₉ : 0 < c * a := mul_pos h₃ h₁
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
