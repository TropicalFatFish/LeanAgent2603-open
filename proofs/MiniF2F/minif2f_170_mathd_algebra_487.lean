import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_487
  (a b c d : ℝ)
  (h₀ : b = a^2)
  (h₁ : a + b = 1)
  (h₂ : d = c^2)
  (h₃ : c + d = 1)
  (h₄ : a ≠ c) :
  Real.sqrt ((a - c)^2 + (b - d)^2)= Real.sqrt 10 := by
  have hA : a + a^2 = 1 := by
    rw [h₀] at h₁
    exact h₁
  have hC : c + c^2 = 1 := by
    rw [h₂] at h₃
    exact h₃
  have h_sum : a + c = -1 := by
    have hA' : a^2 = 1 - a := by linarith
    have hC' : c^2 = 1 - c := by linarith
    have h₁' : a^2 - c^2 = c - a := by linarith
    have h₂' : (a - c) * (a + c + 1) = 0 := by
      ring_nf at h₁' ⊢
      linarith
    have h₃' : a + c + 1 = 0 := by
      apply eq_of_sub_eq_zero
      apply mul_left_cancel₀ (sub_ne_zero.mpr h₄)
      linarith
    linarith
  have h_prod : a * c = -1 := by
    nlinarith [h_sum, hA, hC]
  have h_ac_sq : (a - c)^2 = 5 := by
    calc
      (a - c)^2 = (a + c)^2 - 4 * (a * c) := by ring
      _ = (-1)^2 - 4 * (-1) := by rw [h_sum, h_prod]
      _ = 5 := by norm_num
  have h_bd : (b - d)^2 = 5 := by
    rw [h₀, h₂]
    calc
      (a^2 - c^2)^2 = ((a - c) * (a + c))^2 := by ring
      _ = (a - c)^2 * (a + c)^2 := by ring
      _ = 5 * 1 := by rw [h_ac_sq, h_sum]; ring
      _ = 5 := by norm_num
  have h_final : (a - c)^2 + (b - d)^2 = 10 := by linarith [h_ac_sq, h_bd]
  rw [h_final]
  <;> rfl
