import Mathlib

theorem omni_theorem_2704 (d : ℝ) (t : ℝ) (d1 : ℝ) (v1 : ℝ) (d2 : ℝ) (v2 : ℝ) (h₀ : d = 16) (h₁ : t = 1.5) (h₂ : d1 = 10) (h₃ : v1 = 12) (h₄ : d2 = 6) (h₅ : v2 = (d - d1) / (t - d1 / v1)) : v2 = 9 := by
  rw [h₅]
  rw [h₀, h₁, h₂, h₃]
  norm_num
