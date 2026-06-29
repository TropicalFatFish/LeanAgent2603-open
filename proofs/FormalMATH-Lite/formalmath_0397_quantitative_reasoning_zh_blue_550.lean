import Mathlib

theorem quantitative_reasoning_zh_blue_550
    {a b c : ℝ}
    (f : ℝ → ℝ)
    (hf : ∀ x, f x = x^5 + a * x^3 + b * x + c * Real.sin x + 8)
    (h : f (-2) = 10) :
    f 2 = 6 := by
  have h1 : ∀ x, f x + f (-x) = 16 := by
    intro x
    rw [hf x, hf (-x)]
    simp [Real.sin_neg]
    ring_nf
  have h2 : f 2 + f (-2) = 16 := h1 2
  linarith [h2, h]
