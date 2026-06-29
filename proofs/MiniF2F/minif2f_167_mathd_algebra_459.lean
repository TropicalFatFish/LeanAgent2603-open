import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_459
  (a b c d : ℚ)
  (h₀ : 3 * a = b + c + d)
  (h₁ : 4 * b = a + c + d)
  (h₂ : 2 * c = a + b + d)
  (h₃ : 8 * a + 10 * b + 6 * c = 24) :
  ↑d.den + d.num = 28 := by
  have h₄ : a = 1 := by
    field_simp at h₀ h₁ h₂ h₃ ⊢
    linarith
  have h₅ : d = 13 / 15 := by
    subst_vars
    linarith
  rw [h₅]
  <;> norm_num
  <;> rfl
