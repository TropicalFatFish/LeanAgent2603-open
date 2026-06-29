import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_398
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : 9 * b = 20 * c)
  (h₂ : 7 * a = 4 * b) :
  63 * a = 80 * c := by
  calc
    63 * a = 9 * (7 * a) := by ring
    _ = 9 * (4 * b) := by rw [h₂]
    _ = 4 * (9 * b) := by ring
    _ = 4 * (20 * c) := by rw [h₁]
    _ = 80 * c := by ring
