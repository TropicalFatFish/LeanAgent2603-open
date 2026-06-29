import Mathlib

theorem quantitative_reasoning_zh_blue_558 (a : ℝ) (ha : a > 0) (f : ℝ → ℝ)
    (hf : ∀ x, f x = x ^ 2 + x + a) (m : ℝ) (hm : f m < 0) :
    f (m + 1) > 0 := by
  rw [hf] at hm
  have h1 : m * (m + 1) < 0 := by
    nlinarith [ha]
  have h2 : m + 1 > 0 := by
    by_contra h
    have h_nonpos : m + 1 ≤ 0 := by linarith
    have h_mneg : m < 0 := by linarith
    have h_prod_pos : m * (m + 1) ≥ 0 := by nlinarith
    linarith
  rw [hf]
  nlinarith [ha, h2]
