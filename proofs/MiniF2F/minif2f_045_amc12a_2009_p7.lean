import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem amc12a_2009_p7
  (x : ℝ)
  (n : ℕ)
  (a : ℕ → ℝ)
  (h₁ : ∀ m, a (m + 1) - a m = a (m + 2) - a (m + 1))
  (h₂ : a 1 = 2 * x - 3)
  (h₃ : a 2 = 5 * x - 11)
  (h₄ : a 3 = 3 * x + 1)
  (h₅ : a n = 2009) :
  n = 502 := by
  have hx : x = 4 := by
    have h := h₁ 1
    rw [h₂, h₃, h₄] at h
    linarith
  have ha0 : a 0 = 1 := by
    have h := h₁ 0
    rw [h₂, h₃, hx] at h
    norm_num at h
    linarith
  have hs : ∀ m, a (m + 1) - a m = 4 := by
    intro m
    induction' m with m ih
    · rw [ha0, h₂, hx]
      norm_num
    · have hm := h₁ m
      linarith
  have hd : ∀ m, a (m + 1) = a m + 4 := by
    intro m
    have hm := hs m
    linarith
  have hformula : ∀ m, a m = 4 * m + 1 := by
    intro m
    induction' m with m ih
    · simpa using ha0
    · have hm := hd m
      rw [ih] at hm
      norm_num at hm ⊢
      linarith
  have hn : (4 : ℝ) * n + 1 = 2009 := by
    rw [← hformula n]
    exact h₅
  have hnreal : (n : ℝ) = 502 := by nlinarith
  exact_mod_cast hnreal
