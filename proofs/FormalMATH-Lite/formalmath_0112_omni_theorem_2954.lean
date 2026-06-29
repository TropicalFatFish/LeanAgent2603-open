import Mathlib

theorem omni_theorem_2954 {x y : ℤ} (hx : x > 0) (hy : y > 0)
    (hxy : x * y = 24 ∧ x + y = 11) :
    max x y - min x y = 5 := by
  have h_sum_sq : (x + y) ^ 2 = 121 := by
    rw [hxy.2]
    norm_num
  have h_prod_sq : 4 * (x * y) = 96 := by
    rw [hxy.1]
    norm_num
  have h_diff_sq : (x - y) ^ 2 = 25 := by
    have h : (x - y) ^ 2 = (x + y) ^ 2 - 4 * (x * y) := by ring
    rw [h, h_sum_sq, h_prod_sq]
    norm_num
  have h_abs_diff : abs (x - y) = 5 := by
    have : (x - y) ^ 2 = 25 := h_diff_sq
    cases' le_or_gt 0 (x - y) with h₀ h₀ <;>
      simp_all [abs_of_nonneg, abs_of_neg] <;>
      nlinarith
  cases' le_total x y with h h <;>
    simp_all [abs_of_nonneg, abs_of_neg] <;>
      nlinarith
