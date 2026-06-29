import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem amc12b_2020_p13 :
  Real.sqrt (Real.log 6 / Real.log 2 + Real.log 6 / Real.log 3) = Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3) := by
  have h2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)]
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt]
  · rw [add_sq, Real.sq_sqrt, Real.sq_sqrt]
    · have hprod : Real.sqrt ((Real.log 2)⁻¹ * Real.log 3) * Real.sqrt (Real.log 2 * (Real.log 3)⁻¹) = 1 := by
        rw [← Real.sqrt_mul (by positivity : 0 ≤ (Real.log 2)⁻¹ * Real.log 3) (Real.log 2 * (Real.log 3)⁻¹)]
        have hmul : ((Real.log 2)⁻¹ * Real.log 3) * (Real.log 2 * (Real.log 3)⁻¹) = 1 := by
          field_simp [h2pos.ne', h3pos.ne']
        rw [hmul, Real.sqrt_one]
      ring_nf
      rw [hprod]
      rw [h6]
      field_simp [h2pos.ne', h3pos.ne']
      ring
    · exact div_nonneg h2pos.le h3pos.le
    · exact div_nonneg h3pos.le h2pos.le
  · rw [h6]
    positivity
