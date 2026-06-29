import Mathlib

theorem omni_theorem_2755 (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0)
    (h₂ : (w + r) * (5 / 6 : ℚ) = w) : w = 40 := by
  rw [h₀] at h₂
  field_simp at h₂
  ring_nf at h₂ ⊢
  norm_cast at h₂ ⊢
  linarith
