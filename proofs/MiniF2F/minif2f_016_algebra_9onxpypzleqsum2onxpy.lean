import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_9onxpypzleqsum2onxpy
  (x y z : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) :
  9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by
  have h₁ : 0 < x + y := by linarith
  have h₂ : 0 < y + z := by linarith
  have h₃ : 0 < z + x := by linarith
  have h₄ : 0 < x + y + z := by linarith
  field_simp [h₀.1, h₀.2.1, h₀.2.2, h₁, h₂, h₃, h₄]
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
