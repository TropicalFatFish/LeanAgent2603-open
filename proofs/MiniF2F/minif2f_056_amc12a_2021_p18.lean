import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem amc12a_2021_p18
  (f : ℚ → ℝ)
  (h₀ : ∀x>0, ∀y>0, f (x * y) = f x + f y)
  (h₁ : ∀p, Nat.Prime p → f p = p) :
  f (25 / 11) < 0 := by
  have h₂ : f 25 = 10 := by
    have this : (25 : ℚ) > 0 := by norm_num
    have h₂_left : f (5 * 5) = f 5 + f 5 := by
      have : (5 : ℚ) > 0 := by norm_num
      have : (5 : ℚ) > 0 := by norm_num
      apply h₀
      <;> exact this
    have h₂_right : f 5 = 5 := by
      have : Nat.Prime 5 := by decide
      exact h₁ (5 : ℕ) this
    rw [show (25 : ℚ) = 5 * 5 by norm_num]
    rw [h₂_left, h₂_right]
    <;> norm_num
  have h₃ : f 11 = 11 := by
    have : Nat.Prime 11 := by decide
    exact h₁ (11 : ℕ) this
  have h₄ : f (25 / 11) = f 25 - f 11 := by
    have h₅ : (11 : ℚ) > 0 := by norm_num
    have h₆ : (25 : ℚ) > 0 := by norm_num
    have h₇ : f (25 / 11 * 11) = f (25 / 11) + f 11 := by
      apply h₀
      <;> norm_num
    have h₈ : f (25 / 11 * 11) = f (25 : ℚ) := by
      norm_num
    rw [h₈] at h₇
    linarith
  rw [h₄, h₂, h₃]
  norm_num
