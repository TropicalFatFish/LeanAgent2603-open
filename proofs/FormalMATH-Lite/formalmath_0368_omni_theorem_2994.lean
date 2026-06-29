import Mathlib

theorem omni_theorem_2994 (n h j : ℝ) (h₀ : n = h) (h₁ : j = 161) (h₂ : (n + h + j) / 3 = 171) :
    n = 176 := by
  have h₃ : n + h + j = 513 := by
    calc
      n + h + j = 3 * ((n + h + j) / 3) := by field_simp
      _ = 3 * 171 := by rw [h₂]
      _ = 513 := by norm_num
  rw [h₀] at h₃
  have h₄ : 2 * n + j = 513 := by ring_nf at h₃ ⊢; linarith
  rw [h₁] at h₄
  linarith
