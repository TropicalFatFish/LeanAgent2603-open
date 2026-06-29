import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_209
  (σ : Equiv ℝ ℝ)
  (h₀ : σ.2 2 = 10)
  (h₁ : σ.2 10 = 1)
  (h₂ : σ.2 1 = 2) :
  σ.1 (σ.1 10) = 1 := by
  have h₃ : σ.1 10 = 2 := by
    have h₃' : σ.1 (σ.2 2) = 2 := Equiv.apply_symm_apply σ 2
    rw [h₀] at h₃'
    rw [← h₃']

  have h₄ : σ.1 2 = 1 := by
    have h₄' : σ.1 (σ.2 1) = 1 := Equiv.apply_symm_apply σ 1
    rw [h₂] at h₄'
    rw [← h₄']

  calc
    σ.1 (σ.1 10) = σ.1 2 := by rw [h₃]
  _ = 1 := by rw [h₄]
