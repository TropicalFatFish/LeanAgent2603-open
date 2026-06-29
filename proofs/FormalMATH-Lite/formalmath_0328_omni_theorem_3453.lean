import Mathlib

theorem omni_theorem_3453 (milk flour : ℝ) (h₀ : milk / flour = 50 / 250) (h₁ : flour = 750) :
    milk = 150 := by
  rw [h₁] at h₀
  norm_num at h₀
  field_simp at h₀
  norm_num at h₀
  linarith
