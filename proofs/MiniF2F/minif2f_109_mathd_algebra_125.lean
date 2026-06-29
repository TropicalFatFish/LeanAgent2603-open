import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_125
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : 5 * x = y)
  (h₂ : (↑x - (3:ℤ)) + (y - (3:ℤ)) = 30) :
  x = 6 := by
  have h₃ : ∀ z : ℕ, z > 0 → (z : ℤ) - (3 : ℤ) = (z - 3 : ℤ) := by
    intro z h
    have h₄ : (z : ℤ) > 0 := by exact_mod_cast h
    linarith

  have h₄ : 6 * x = 36 := by
    have h₅ : (↑x - (3 : ℤ)) + (↑y - (3 : ℤ)) = 30 := h₂
    have h₆ : ↑y = 5 * ↑x := by
      norm_cast at h₁ ⊢
      exact h₁.symm
    rw [h₆] at h₅
    ring_nf at h₅ ⊢
    omega

  have h₅ : 6 * x = 36 := h₄
  have h₆ : x = 6 := by
    have h₇ : 6 * x = 36 := h₅
    have h₈ : x = 6 := by
      omega
    exact h₈

  exact h₆
