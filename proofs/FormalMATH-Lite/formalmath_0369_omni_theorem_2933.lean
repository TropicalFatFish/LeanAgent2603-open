import Mathlib

theorem omni_theorem_2933 (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) :
    L = 42 := by
  ring_nf at h₁ ⊢
  linarith
