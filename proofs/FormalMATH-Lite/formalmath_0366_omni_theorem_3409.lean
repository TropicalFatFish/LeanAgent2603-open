import Mathlib

theorem omni_theorem_3409 {x : ℝ} (hx : x * (1 - 20 / 100) = 112) :
    x * (1 - 30 / 100) = 98 := by
  have h1 : x * (4 / 5) = 112 := by
    norm_num at hx
    exact hx

  have h2 : x = 140 := by
    have h3 : x = 140 := by
      field_simp at h1
      nlinarith
    exact h3

  rw [h2]
  norm_num
