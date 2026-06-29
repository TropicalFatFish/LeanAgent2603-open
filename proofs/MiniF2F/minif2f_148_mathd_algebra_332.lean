import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_332
  (x y : ℝ)
  (h₀ : (x + y) / 2 = 7)
  (h₁ : Real.sqrt (x * y) = Real.sqrt 19) :
  x^2 + y^2 = 158 := by
  have h_sum : x + y = 14 := by
    field_simp at h₀
    linarith

  have h_prod : x * y = 19 := by
    have h₂ : 0 ≤ x * y := by
      by_contra h
      have h' : x * y ≤ 0 := by linarith
      have h_sqrt : Real.sqrt (x * y) = 0 := Real.sqrt_eq_zero_of_nonpos h'
      rw [h₁] at h_sqrt
      have h₄ : 0 < Real.sqrt 19 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 19)
      linarith [h_sqrt, h₄]
    have h₃ : Real.sqrt (x * y) = Real.sqrt 19 := h₁
    have h₄ : x * y = 19 := by
      have h₅ : 0 ≤ x * y := h₂
      have h₆ : 0 ≤ (19 : ℝ) := by norm_num
      rw [Real.sqrt_inj h₅ h₆] at h₃
      exact h₃
    exact h₄

  calc
    x^2 + y^2 = (x + y)^2 - 2 * (x * y) := by ring
    _ = 14^2 - 2 * 19 := by rw [h_sum, h_prod]
    _ = 196 - 38 := by norm_num
    _ = 158 := by norm_num
