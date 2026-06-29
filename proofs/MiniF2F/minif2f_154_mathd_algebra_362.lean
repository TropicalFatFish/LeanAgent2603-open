import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_362
  (a b : ℝ)
  (h₀ : a^2 * b^3 = 32 / 27)
  (h₁ : a / b^3 = 27 / 4) :
  a + b = 8 / 3 := by
  have h₂ : b ≠ 0 := by
    intro h
    rw [h] at h₁
    norm_num at h₁
  have h₃ : a = (27 / 4) * b^3 := by
    field_simp [h₂] at h₁ ⊢
    linarith
  rw [h₃] at h₀
  have h₆ : (27 / 4)^2 * b^9 = 32 / 27 := by
    ring_nf at h₀ ⊢
    linarith
  have h₇ : b^9 = (2 / 3 : ℝ)^9 := by
    field_simp [pow_ne_zero 3 h₂] at h₆ ⊢
    ring_nf at h₆ ⊢
    norm_num at h₆ ⊢
    nlinarith
  have h₈ : b = 2 / 3 := by
    exact (show Odd 9 by norm_num).pow_inj.mp h₇
  have h₉ : a = 2 := by
    rw [h₈] at h₃
    norm_num at h₃ ⊢
    linarith
  rw [h₉, h₈]
  norm_num
