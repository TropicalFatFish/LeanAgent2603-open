import Mathlib

theorem omni_theorem_2828 (d : ℝ) (h : d = 30) (v1 v2 : ℝ)
    (h1 : v1 = 20) (h2 : v2 = 15) :
    (d / v2 - d / v1) * 60 = 30 := by
  rw [h, h1, h2]
  norm_num
