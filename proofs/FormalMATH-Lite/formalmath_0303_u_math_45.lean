import Mathlib

theorem u_math_45
    {j z d f m y : ℝ}
    (h₀ : 8.6 = 6 * j + 4 * j)
    (h₁ : 12 * z - (4 * z + 6) = 82)
    (h₂ : 5.4 * d - 2.3 * d + 3 * (d - 4) = 16.67)
    (h₃ : 2.6 * f - 1.3 * (3 * f - 4) = 6.5)
    (h₄ : -5.3 * m + (-3.9 * m) - 17 = -94.28)
    (h₅ : 6 * (3.5 * y + 4.2) - 2.75 * y = 134.7) :
    j = 0.86 ∧ z = 11 ∧ d = 47 / 10 ∧ f = -1 ∧ m = 42 / 5 ∧ y = 6 := by
  have hj : j = 0.86 := by
    have : 10 * j = 8.6 := by linarith
    norm_num at this ⊢
    linarith

  have hz : z = 11 := by
    have : 8 * z = 88 := by linarith
    norm_num at this ⊢
    linarith

  have hd : d = 47 / 10 := by
    have : 6.1 * d = 28.67 := by linarith
    norm_num at this ⊢
    linarith

  have hf : f = -1 := by
    have : 1.3 * f = -1.3 := by linarith
    norm_num at this ⊢
    linarith

  have hm : m = 42 / 5 := by
    have : 9.2 * m = 77.28 := by linarith
    norm_num at this ⊢
    linarith

  have hy : y = 6 := by
    have : 18.25 * y = 109.5 := by linarith
    norm_num at this ⊢
    linarith

  exact ⟨hj, hz, hd, hf, hm, hy⟩
