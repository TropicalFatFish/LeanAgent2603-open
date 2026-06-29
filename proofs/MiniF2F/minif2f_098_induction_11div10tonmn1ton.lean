import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem induction_11div10tonmn1ton
  (n : ℕ) :
  11 ∣ (10^n - (-1 : ℤ)^n) := by
  induction n with
  | zero =>
    simp [Int.pow_zero, Int.neg_pow]
  | succ n ih =>
    have h : 10^(n+1) - (-1 : ℤ)^(n+1) = 10 * (10^n - (-1 : ℤ)^n) + 11 * (-1 : ℤ)^n := by
      simp only [Int.pow_succ, mul_comm] at *
      ring
    rw [h]
    have h1 : 11 ∣ (10 : ℤ) * (10^n - (-1 : ℤ)^n) := by
      apply dvd_mul_of_dvd_right
      exact ih
    have h2 : 11 ∣ 11 * (-1 : ℤ)^n := by
      apply dvd_mul_right
    exact dvd_add h1 h2
