import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem amc12a_2009_p6
  (m n p q : ℝ)
  (h₀ : p = 2 ^ m)
  (h₁ : q = 3 ^ n) :
  p^(2 * n) * (q^m) = 12^(m * n) := by
  calc
    p ^ (2 * n) * q ^ m = (2 ^ m) ^ (2 * n) * (3 ^ n) ^ m := by simp [h₀, h₁]
    _ = 2 ^ (m * (2 * n)) * 3 ^ (n * m) := by
      have h₂ : (0 : ℝ) ≤ 2 := by norm_num
      have h₃ : (0 : ℝ) ≤ 3 := by norm_num
      simp [Real.rpow_mul]
    _ = 2 ^ (2 * m * n) * 3 ^ (m * n) := by
      simp [mul_assoc, mul_comm, mul_left_comm]
    _ = (2 ^ 2 : ℝ) ^ (m * n) * 3 ^ (m * n) := by
      have h₄ : (0 : ℝ) ≤ 2 := by norm_num
      simp [rpow_mul h₄, mul_assoc]
    _ = 4 ^ (m * n) * 3 ^ (m * n) := by norm_num
    _ = (4 * 3 : ℝ) ^ (m * n) := by
      have h₄ : (0 : ℝ) ≤ 4 := by norm_num
      have h₅ : (0 : ℝ) ≤ 3 := by norm_num
      rw [Real.mul_rpow h₄ h₅]
    _ = 12 ^ (m * n) := by norm_num
