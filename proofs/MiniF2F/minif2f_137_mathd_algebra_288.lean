import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_288
  (x y : ℝ)
  (n : NNReal)
  (h₀ : x < 0 ∧ y < 0)
  (h₁ : abs y = 6)
  (h₂ : Real.sqrt ((x - 8)^2 + (y - 3)^2) = 15)
  (h₃ : Real.sqrt (x^2 + y^2) = Real.sqrt n) :
  n = 52 := by
  have h_y : y = -6 := by
    rw [abs_of_neg h₀.2] at h₁
    linarith

  have h_quadratic : (x - 8)^2 + (y - 3)^2 = 225 := by
    have h₂_nonneg : 0 ≤ ((x - 8)^2 + (y - 3)^2) := by nlinarith
    have h₂_sq : ((x - 8)^2 + (y - 3)^2) = (Real.sqrt ((x - 8)^2 + (y - 3)^2))^2 := by
      rw [Real.sq_sqrt h₂_nonneg]
    rw [h₂_sq, h₂]
    norm_num

  have h_x : x = -4 := by
    rw [h_y] at h_quadratic
    nlinarith

  have h_xy_sum_sq : x^2 + y^2 = 52 := by
    rw [h_x, h_y]
    norm_num

  have h_n : (n : ℝ) = 52 := by
    have h₃_nonneg : 0 ≤ x^2 + y^2 := by nlinarith
    have h_n_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast n.prop
    have h₃_sq : (x^2 + y^2) = (n : ℝ) := by
      calc
        (x^2 + y^2) = (Real.sqrt (x^2 + y^2))^2 := by
          rw [Real.sq_sqrt] <;> nlinarith
        _ = (Real.sqrt n)^2 := by rw [h₃]
        _ = (n : ℝ) := by
          rw [Real.sq_sqrt] <;> nlinarith
    linarith

  exact_mod_cast h_n
