import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_158
  (a : ℕ)
  (h₀ : Even a)
  (h₁ : ∑ k ∈ Finset.range 8, (2 * k + 1) - ∑ k ∈ Finset.range 5, (a + 2 * k) = (4:ℤ)) :
  a = 8 := by
  simp only [Finset.sum_const, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, zero_add] at h₁
  norm_num at h₁
  have h₂ : a = 8 := by
    omega
  exact h₂
