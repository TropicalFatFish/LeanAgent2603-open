import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_598
  (a b c d : ℝ)
  (h₁ : ((4:ℝ)^a) = 5)
  (h₂ : ((5:ℝ)^b) = 6)
  (h₃ : ((6:ℝ)^c) = 7)
  (h₄ : ((7:ℝ)^d) = 8) :
  a * b * c * d = 3 / 2 := by
  have h₁' : a * Real.log 4 = Real.log 5 := by
    have h₁eq : (4 : ℝ) ^ a = 5 := by exact_mod_cast h₁
    have h₁log : Real.log ((4 : ℝ) ^ a) = Real.log 5 := by rw [h₁eq]
    rw [Real.log_rpow (by norm_num : (0:ℝ) < 4) a] at h₁log
    exact h₁log

  have h₂' : b * Real.log 5 = Real.log 6 := by
    have h₂eq : (5 : ℝ) ^ b = 6 := by exact_mod_cast h₂
    have h₂log : Real.log ((5 : ℝ) ^ b) = Real.log 6 := by rw [h₂eq]
    rw [Real.log_rpow (by norm_num : (0:ℝ) < 5) b] at h₂log
    exact h₂log

  have h₃' : c * Real.log 6 = Real.log 7 := by
    have h₃eq : (6 : ℝ) ^ c = 7 := by exact_mod_cast h₃
    have h₃log : Real.log ((6 : ℝ) ^ c) = Real.log 7 := by rw [h₃eq]
    rw [Real.log_rpow (by norm_num : (0:ℝ) < 6) c] at h₃log
    exact h₃log

  have h₄' : d * Real.log 7 = Real.log 8 := by
    have h₄eq : (7 : ℝ) ^ d = 8 := by exact_mod_cast h₄
    have h₄log : Real.log ((7 : ℝ) ^ d) = Real.log 8 := by rw [h₄eq]
    rw [Real.log_rpow (by norm_num : (0:ℝ) < 7) d] at h₄log
    exact h₄log

  have h₁_nonzero : Real.log 4 ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    <;> norm_num

  have h₂_nonzero : Real.log 5 ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    <;> norm_num

  have h₃_nonzero : Real.log 6 ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    <;> norm_num

  have h₄_nonzero : Real.log 7 ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    <;> norm_num

  have h₁_expr : a = Real.log 5 / Real.log 4 := by
    have h_temp : a = Real.log 5 / Real.log 4 := by
      field_simp [h₁_nonzero] at h₁' ⊢
      linarith
    exact h_temp

  have h₂_expr : b = Real.log 6 / Real.log 5 := by
    have h_temp : b = Real.log 6 / Real.log 5 := by
      field_simp [h₂_nonzero] at h₂' ⊢
      linarith
    exact h_temp

  have h₃_expr : c = Real.log 7 / Real.log 6 := by
    have h_temp : c = Real.log 7 / Real.log 6 := by
      field_simp [h₃_nonzero] at h₃' ⊢
      linarith
    exact h_temp

  have h₄_expr : d = Real.log 8 / Real.log 7 := by
    have h_temp : d = Real.log 8 / Real.log 7 := by
      field_simp [h₄_nonzero] at h₄' ⊢
      linarith
    exact h_temp

  rw [h₁_expr, h₂_expr, h₃_expr, h₄_expr]

  have h₄_nonzero' : Real.log 4 ≠ 0 := h₁_nonzero
  have h₃_nonzero' : Real.log 5 ≠ 0 := h₂_nonzero
  have h₂_nonzero' : Real.log 6 ≠ 0 := h₃_nonzero
  have h₁_nonzero' : Real.log 7 ≠ 0 := h₄_nonzero

  field_simp [h₄_nonzero', h₃_nonzero', h₂_nonzero', h₁_nonzero']
  <;> ring_nf at *
  <;> simp_all
  <;> norm_num
  <;> rw [show (8 : ℝ) = (2 : ℝ) ^ 3 by norm_num]
  <;> rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num]
  <;> simp_all
  <;> norm_num
  <;> linarith
