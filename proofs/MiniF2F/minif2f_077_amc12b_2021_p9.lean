import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem amc12b_2021_p9 :
  (Real.log 80 / Real.log 2) / (Real.log 2 / Real.log 40) - (Real.log 160 / Real.log 2) / (Real.log 2 / Real.log 20) = 2 := by
  have h : Real.log 2 ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  have h5 : Real.log 5 ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  have h80 : Real.log 80 = 4 * Real.log 2 + Real.log 5 := by
    rw [show Real.log 80 = Real.log (2 ^ 4 * 5) by norm_num]
    simp [Real.log_mul, Real.log_pow]
    <;> norm_num
  have h40 : Real.log 40 = 3 * Real.log 2 + Real.log 5 := by
    rw [show Real.log 40 = Real.log (2 ^ 3 * 5) by norm_num]
    simp [Real.log_mul, Real.log_pow]
    <;> norm_num
  have h160 : Real.log 160 = 5 * Real.log 2 + Real.log 5 := by
    rw [show Real.log 160 = Real.log (2 ^ 5 * 5) by norm_num]
    simp [Real.log_mul, Real.log_pow]
    <;> norm_num
  have h20 : Real.log 20 = 2 * Real.log 2 + Real.log 5 := by
    rw [show Real.log 20 = Real.log (2 ^ 2 * 5) by norm_num]
    simp [Real.log_mul, Real.log_pow]
    <;> norm_num
  rw [h80, h40, h160, h20]
  field_simp [h, h5]
  ring_nf
  <;> norm_num [mul_add, add_mul, sub_mul, mul_sub]
  <;> linarith
