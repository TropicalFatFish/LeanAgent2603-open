import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_338
  (a b c : ℝ)
  (h₀ : 3 * a + b + c = -3)
  (h₁ : a + 3 * b + c = 9)
  (h₂ : a + b + 3 * c = 19) :
  a * b * c = -56 := by
  have h₃ : a + b + c = 5 := by
    calc
      a + b + c = (3 * a + b + c + a + 3 * b + c + a + b + 3 * c) / 5 := by
        field_simp
        linarith
      _ = (-3 + 9 + 19) / 5 := by linarith
      _ = 5 := by norm_num
  have h₄ : a = -4 := by
    have : 2 * a = -8 := by
      linarith
    linarith
  have h₅ : b = 2 := by
    have : 2 * b = 4 := by
      linarith
    linarith
  have h₆ : c = 7 := by
    have : 2 * c = 14 := by
      linarith
    linarith
  rw [h₄, h₅, h₆]
  norm_num
