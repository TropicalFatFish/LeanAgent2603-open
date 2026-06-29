import Mathlib

theorem omni_theorem_3201 (total_sum : ℝ) (h₀ : total_sum = 50 * 76) (group₁_sum : ℝ)
    (h₁ : group₁_sum = 40 * 80) :
    (total_sum - group₁_sum) / 10 = 60 := by
  rw [h₀, h₁]
  norm_num
