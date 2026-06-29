import Mathlib

open Real Set
open scoped BigOperators

theorem quantitative_reasoning_zh_blue_561 (a : ℝ) (f : ℝ → ℝ)
  (hf : ∀ x, f x = x ^ 2 + a * x + 3 - a)
  (h : ∀ x ∈ Icc (-2) 2, f x ≥ 0) :
  a ∈ Icc (-7) 2 := by
  have h_2_in : (2 : ℝ) ∈ Icc (-2) 2 := by norm_num
  have h_f_2 : f 2 ≥ 0 := h 2 h_2_in
  have h_f_2_eq : f 2 = 7 + a := by
    rw [hf 2]
    ring_nf
  rw [h_f_2_eq] at h_f_2
  have h_lower : -7 ≤ a := by linarith

  have h_neg1_in : (-1 : ℝ) ∈ Icc (-2) 2 := by norm_num
  have h_f_neg1 : f (-1) ≥ 0 := h (-1) h_neg1_in
  have h_f_neg1_eq : f (-1) = 4 - 2 * a := by
    rw [hf (-1)]
    ring_nf
  rw [h_f_neg1_eq] at h_f_neg1
  have h_upper : a ≤ 2 := by linarith

  exact ⟨h_lower, h_upper⟩
