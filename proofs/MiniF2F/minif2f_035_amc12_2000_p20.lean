import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem amc12_2000_p20
  (x y z : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
  (h₁ : x + 1/y = 4)
  (h₂ : y + 1/z = 1)
  (h₃ : z + 1/x = 7/3) :
  x*y*z = 1 := by
  rcases h₀ with ⟨hx, hy, hz⟩
  have h_pos : 0 < x * y * z := by positivity
  have h_sum : (x + 1/y) + (y + 1/z) + (z + 1/x) = x + y + z + 1/x + 1/y + 1/z := by
    ring
  have h_sum_val : x + y + z + 1/x + 1/y + 1/z = 22/3 := by
    calc
      x + y + z + 1/x + 1/y + 1/z
        = (x + 1/y) + (y + 1/z) + (z + 1/x) := by rw [h_sum]
      _ = 4 + 1 + 7/3 := by rw [h₁, h₂, h₃]
      _ = 22/3 := by norm_num
  have h_prod : (x + 1/y) * (y + 1/z) * (z + 1/x) = x * y * z + 1/(x * y * z) + x + y + z + 1/x + 1/y + 1/z := by
    field_simp [hx.ne', hy.ne', hz.ne', h_pos.ne']
    ring_nf
  have h_prod_val : (x + 1/y) * (y + 1/z) * (z + 1/x) = 28/3 := by
    calc
      (x + 1/y) * (y + 1/z) * (z + 1/x) = 4 * 1 * (7/3) := by rw [h₁, h₂, h₃]
      _ = 28/3 := by norm_num
  have h_eq : x * y * z + 1/(x * y * z) + x + y + z + 1/x + 1/y + 1/z = 28/3 := by
    linarith [h_prod, h_prod_val, h_sum_val]
  have h_main : x * y * z + 1/(x * y * z) = 2 := by
    linarith [h_eq, h_sum_val]
  have h_xyz_eq_1 : x * y * z = 1 := by
    have h : x * y * z + 1/(x * y * z) - 2 = (x * y * z - 1)^2 / (x * y * z) := by
      field_simp [h_pos.ne']
      ring
    have h₀ : x * y * z + 1/(x * y * z) - 2 = 0 := by linarith
    have h₁ : (x * y * z - 1)^2 / (x * y * z) = 0 := by linarith [h, h₀]
    have h₂ : (x * y * z - 1)^2 = 0 := by
      have := h₁
      field_simp [this, h_pos.ne'] at this
      linarith
    have h₃ : (x * y * z - 1)^2 = 0 := by linarith
    exact (by nlinarith [sq_nonneg (x * y * z - 1)])
  exact h_xyz_eq_1
