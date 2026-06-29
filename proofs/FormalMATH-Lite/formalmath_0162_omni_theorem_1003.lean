import Mathlib

open Real

theorem omni_theorem_1003 (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z)
(hxyz : x * y + z = (x + z) * (y + z)) :
    x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27 := by
  have hsum : x + y + z = 1 := by
    have h1 : x * z + y * z + z ^ 2 = z := by
      have h2 : x * y + z = x * y + x * z + y * z + z ^ 2 := by
        rw [mul_add, add_mul] at hxyz
        ring_nf at hxyz ⊢
        linarith [hxyz]
      linarith
    have h3 : z * (x + y + z) = z := by linarith
    have h4 : x + y + z = 1 := by
      apply mul_left_cancel₀ (ne_of_gt hzpos)
      linarith
    exact h4

  have h_le : x * y * z ≤ 1 / 27 := by
    have h1 : 0 < x * y * z := mul_pos (mul_pos hxpos hypos) hzpos
    have h2 : x * y * z ≤ ((x + y + z) / 3) ^ 3 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
    calc
      x * y * z ≤ ((x + y + z) / 3) ^ 3 := h2
      _ = (1 / 3 : ℝ) ^ 3 := by rw [hsum]
      _ = 1 / 27 := by norm_num

  have h_eq : ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27 := by
    use 1 / 3, 1 / 3, 1 / 3
    exact ⟨by norm_num, by norm_num, by norm_num, by
      norm_num, by
      norm_num⟩

  exact ⟨h_le, h_eq⟩
