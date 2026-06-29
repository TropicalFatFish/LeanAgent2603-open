import Mathlib

theorem omni_theorem_3469 {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0)
    (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z) :
    z = 40 / 100 * y := by
  have h_eq : 20 / 100 * y = 50 / 100 * z := by linarith [hxy, hxz]
  have h_yz : z = 2 / 5 * y := by
    rw [show (20 / 100 : ℝ) = 1 / 5 by norm_num] at h_eq
    rw [show (50 / 100 : ℝ) = 1 / 2 by norm_num] at h_eq
    apply mul_left_cancel₀ (show (1/2 : ℝ) ≠ 0 by norm_num)
    field_simp at h_eq ⊢
    ring_nf at h_eq ⊢
    linarith [h_eq]
  rw [show (40 / 100 : ℝ) = 2 / 5 by norm_num]
  exact h_yz
