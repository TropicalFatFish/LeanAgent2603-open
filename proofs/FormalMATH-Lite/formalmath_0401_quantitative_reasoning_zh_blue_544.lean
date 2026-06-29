import Mathlib

theorem quantitative_reasoning_zh_blue_544 {f : ℝ → ℝ} (h : ∀ x, f (x - 1 / x) = x ^ 2 + 1 / x ^ 2 + 1) :
    ∀ x, f (x + 1) = x ^ 2 + 2 * x + 4 := by
  have h0 := h 0
  have h1 := h 1
  norm_num at h0 h1
  linarith
