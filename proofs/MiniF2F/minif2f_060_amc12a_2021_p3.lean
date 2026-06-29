import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem amc12a_2021_p3
  (x y : ℕ)
  (h₀ : x + y = 17402)
  (h₁ : 10∣x)
  (h₂ : x / 10 = y) :
  ↑x - ↑y = (14238:ℤ) := by
  have h₃ : x = 10 * y := by
    have h₄ : x = 10 * (x / 10) := by
      rw [Nat.mul_div_cancel' h₁]
    rw [h₂] at h₄
    linarith
  have h₄ : 11 * y = 17402 := by
    linarith
  have h₅ : y = 1582 := by
    omega
  have h₆ : x = 15820 := by
    rw [h₃, h₅]
    <;> norm_num
  rw [h₆, h₅]
  <;> norm_num
  <;> simp [h₃, h₄, h₅, h₆]
  <;> rfl
