import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_141
  (a b : ℝ)
  (h₁ : (a * b)=180)
  (h₂ : 2 * (a + b)=54) :
  (a^2 + b^2) = 369 := by
  have h₃ : a + b = 27 := by linarith
  have h₄ : (a + b)^2 = 729 := by
    calc
      (a + b)^2 = 27^2 := by rw [h₃]
      _ = 729 := by norm_num
  have h₅ : a^2 + b^2 = 369 := by
    calc
      a^2 + b^2 = (a + b)^2 - 2 * (a * b) := by ring
      _ = 729 - 2 * 180 := by rw [h₄, h₁]
      _ = 369 := by norm_num
  exact h₅
