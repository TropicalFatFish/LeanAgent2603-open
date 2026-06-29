import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1
  (x : ℝ)
  (h₀ : abs (x - 1) + abs x + abs (x + 1) = x + 2) :
  0 ≤ x ∧ x ≤ 1 := by
  have h₁ : x ≥ 0 := by
    by_contra h
    have h₂ : x < 0 := by linarith
    have h₃ : x - 1 < 0 := by linarith
    rw [abs_of_neg h₃, abs_of_neg h₂] at h₀
    by_cases h₄ : x + 1 ≥ 0
    ·
      rw [abs_of_nonneg h₄] at h₀
      linarith
    ·
      rw [abs_of_neg (by linarith)] at h₀
      linarith

  have h₂ : x ≤ 1 := by
    by_contra h
    have h₃ : x > 1 := by linarith
    have h₄ : x - 1 > 0 := by linarith
    have h₅ : x + 1 > 0 := by linarith
    have h₆ : x > 0 := by linarith
    rw [abs_of_pos h₄, abs_of_pos h₆, abs_of_pos h₅] at h₀
    linarith

  exact ⟨h₁, h₂⟩
