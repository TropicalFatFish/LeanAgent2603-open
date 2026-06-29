import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_129
  (a : ℝ)
  (h₀ : a ≠ 0)
  (h₁ : 8⁻¹ / 4⁻¹ - a⁻¹ = 1) :
  a = -2 := by
  have h₂ : a⁻¹ = -1 / 2 := by
    field_simp at h₁ ⊢
    ring_nf at h₁ ⊢
    linarith
  have h₃ : a = -2 := by
    apply_fun (fun x => x⁻¹) at h₂
    field_simp [h₀] at h₂ ⊢
    linarith
  exact h₃
