import Mathlib

theorem u_math_1027 (x : ℝ) :
    abs (3 * x - 11) = 4 * x - 3 ↔ x = 2 := by
  constructor
  · intro h
    have h_nonneg : 4 * x - 3 ≥ 0 := by
      rw [← h]
      exact abs_nonneg (3 * x - 11)
    by_cases h1 : (3 * x - 11) ≥ 0
    ·
      have : abs (3 * x - 11) = 3 * x - 11 := abs_of_nonneg h1
      rw [this] at h
      linarith
    ·
      have : abs (3 * x - 11) = -(3 * x - 11) := abs_of_neg (by linarith)
      rw [this] at h
      linarith
  · intro h
    rw [h]
    norm_num
