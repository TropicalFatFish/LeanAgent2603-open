import Mathlib

theorem u_math_523 (t : ℝ) (ht : 0 ≤ t) :
    80000 + 2200 * t = 120000 ↔ t = 200 / 11 := by
  constructor
  · intro h
    have h1 : 2200 * t = 40000 := by linarith
    have h2 : t = 40000 / 2200 := by
      field_simp at h1 ⊢
      linarith
    norm_num [h2]
  · intro h
    rw [h]
    ring
