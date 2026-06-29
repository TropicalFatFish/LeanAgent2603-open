import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem amc12b_2021_p3
  (x : ℝ)
  (h₀ : 2 + 1 / (1 + 1 / (2 + 2 / (3 + x))) = 144 / 53) :
  x = 3 / 4 := by
  have h₁ : 1 / (1 + 1 / (2 + 2 / (3 + x))) = 38 / 53 := by
    rw [← sub_eq_zero] at h₀
    field_simp at h₀ ⊢
    ring_nf at h₀ ⊢
    linarith
  have h₂ : 1 + 1 / (2 + 2 / (3 + x)) = 53 / 38 := by
    have h := congrArg (fun t : ℝ => 1 / t) h₁
    norm_num at h
    simpa [one_div_one_div] using h
  have h₃ : 1 / (2 + 2 / (3 + x)) = 15 / 38 := by
    rw [← sub_eq_zero] at h₂
    field_simp at h₂ ⊢
    ring_nf at h₂ ⊢
    linarith
  have h₄ : 2 + 2 / (3 + x) = 38 / 15 := by
    have h := congrArg (fun t : ℝ => 1 / t) h₃
    norm_num at h
    simpa [one_div_one_div] using h
  have h₅ : 2 / (3 + x) = 8 / 15 := by
    rw [← sub_eq_zero] at h₄
    field_simp at h₄ ⊢
    ring_nf at h₄ ⊢
    linarith
  have h₆ : 3 + x = 15 / 4 := by
    have hden : 3 + x ≠ 0 := by
      intro hden
      rw [hden] at h₅
      norm_num at h₅
    field_simp [hden] at h₅
    ring_nf at h₅ ⊢
    linarith
  linarith
