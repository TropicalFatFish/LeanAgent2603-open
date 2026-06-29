import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_2varlineareq_fp3zeq11_3tfm1m5zeqn68_feqn10_zeq7
  (f z: ℂ)
  (h₀ : f + 3*z = 11)
  (h₁ : 3*(f - 1) - 5*z = -68) :
  f = -10 ∧ z = 7 := by
  have h₁' : 3*f - 5*z = -65 := by
    calc
      3*f - 5*z = 3*(f - 1) - 5*z + 3 := by ring
      _ = -68 + 3 := by rw [h₁]
      _ = -65 := by ring

  have h₂ : f = 11 - 3*z := by
    have : f + 3*z = 11 := h₀
    rw [← this]
    ring

  have h₃ : z = 7 := by
    have : 3*(11 - 3*z) - 5*z = -65 := by
      rw [h₂] at h₁'
      exact h₁'
    have : 33 - 9*z - 5*z = -65 := by
      calc
        33 - 9*z - 5*z = 3*(11 - 3*z) - 5*z := by ring
        _ = -65 := by exact this
    have : 33 - 14*z = -65 := by
      calc
        33 - 14*z = 33 - 9*z - 5*z := by ring
        _ = -65 := by exact this
    have : -14*z = -98 := by
      calc
        -14*z = 33 - 14*z - 33 := by ring
        _ = -65 - 33 := by rw [this]
        _ = -98 := by ring
    have : z = 7 := by
      apply mul_left_cancel₀ (show (-14 : ℂ) ≠ 0 by norm_num)
      calc
        -14*z = -98 := by exact this
        _ = -14*7 := by ring
    exact this

  have h₄ : f = -10 := by
    rw [h₂, h₃]
    ring

  exact ⟨h₄, h₃⟩
