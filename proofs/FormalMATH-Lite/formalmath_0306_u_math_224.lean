import Mathlib

theorem u_math_224 (x y : ℝ) :
    x * (x - 2) + y * (y + 4) + 5 = 0 ↔ (x = 1 ∧ y = -2) := by
  constructor
  · intro h
    have h1 : x = 1 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y + 2)]
    have h2 : y = -2 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y + 2)]
    exact ⟨h1, h2⟩
  · rintro ⟨hx, hy⟩
    rw [hx, hy]
    norm_num
