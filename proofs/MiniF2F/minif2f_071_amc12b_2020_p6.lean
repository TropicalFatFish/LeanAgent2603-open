import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem amc12b_2020_p6
  (n : ℕ)
  (h₀ : 9 ≤ n) :
  ∃ (x : ℕ), (x : ℝ)^2 = (Nat.factorial (n + 2) - Nat.factorial (n + 1)) / n ! := by
  use n + 1
  rw [Nat.factorial_succ (n + 1)] at *
  rw [Nat.factorial_succ n] at *
  simp_all [Nat.factorial_ne_zero]
  <;> field_simp
  <;> ring_nf
  <;> norm_cast
  <;> omega
