import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem imo_1960_p2
  (x : ℝ)
  (h₀ : 0 ≤ 1 + 2 * x)
  (h₁ : (1 - Real.sqrt (1 + 2 * x))^2 ≠ 0)
  (h₂ : (4 * x^2) / (1 - Real.sqrt (1 + 2*x))^2 < 2*x + 9)
  (h₃ : x ≠ 0) :
  -(1 / 2) ≤ x ∧ x < 45 / 8 := by
  have h_left : -(1 / 2) ≤ x := by
    have : 0 ≤ 1 + 2 * x := h₀
    linarith

  have h_right : x < 45 / 8 := by
    by_contra h
    have : x ≥ 45 / 8 := by linarith
    have h₄ : 0 < 2 * x + 9 := by linarith
    have h₅ : 0 ≤ 1 + 2 * x := by linarith [h₀]
    have h₆ : 0 ≤ Real.sqrt (1 + 2 * x) := Real.sqrt_nonneg (1 + 2 * x)
    have h₇ : Real.sqrt (1 + 2 * x) ^ 2 = 1 + 2 * x := by rw [Real.sq_sqrt (by linarith)]
    have h₈ : 0 < (1 - Real.sqrt (1 + 2 * x)) ^ 2 := by
      have : (1 - Real.sqrt (1 + 2 * x)) ^ 2 > 0 := by
        nlinarith [h₁]
      exact this
    have h₉ : (4 * x ^ 2) / (1 - Real.sqrt (1 + 2 * x)) ^ 2 ≥ 2 * x + 9 := by
      have hs_ge : (7 / 2 : ℝ) ≤ Real.sqrt (1 + 2 * x) := by
        apply Real.le_sqrt_of_sq_le
        nlinarith
      have hfac : 0 ≤ (1 - Real.sqrt (1 + 2 * x)) ^ 2 * (2 * Real.sqrt (1 + 2 * x) - 7) := by
        apply mul_nonneg
        · positivity
        · nlinarith
      change 2 * x + 9 ≤ (4 * x ^ 2) / (1 - Real.sqrt (1 + 2 * x)) ^ 2
      rw [le_div_iff₀ h₈]
      nlinarith
    linarith [h, h₂, h₉]
  exact ⟨h_left, h_right⟩
