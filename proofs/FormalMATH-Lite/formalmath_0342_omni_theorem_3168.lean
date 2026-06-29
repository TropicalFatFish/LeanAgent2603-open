import Mathlib

theorem omni_theorem_3168 {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy : x * y = 1 / 9) (hxy1 : x * (y + 1) = 7 / 9) (hxy2 : y * (x + 1) = 5 / 18) :
    (x + 1) * (y + 1) = 35 / 18 := by

  have hxy1' : x * y + x = 7 / 9 := by
    ring_nf at hxy1
    linarith

  have hxy2' : x * y + y = 5 / 18 := by
    ring_nf at hxy2
    linarith

  have h3 : x = 2 / 3 := by
    rw [hxy] at hxy1'
    linarith

  have h4 : y = 1 / 6 := by
    rw [hxy] at hxy2'
    linarith

  calc
    (x + 1) * (y + 1) = (2 / 3 + 1) * (1 / 6 + 1) := by rw [h3, h4]
    _ = 35 / 18 := by norm_num
