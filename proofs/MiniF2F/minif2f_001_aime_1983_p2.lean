import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1983_p2
  (x p : ℝ)
  (f : ℝ → ℝ)
  (h₀ : 0 < p ∧ p < 15)
  (h₁ : p ≤ x ∧ x ≤ 15)
  (h₂ : f x = abs (x - p) + abs (x - 15) + abs (x - p - 15)) :
  15 ≤ f x := by
  have h₃ : 0 < p := h₀.1
  have h₄ : p < 15 := h₀.2
  have h₅ : p ≤ x := h₁.1
  have h₆ : x ≤ 15 := h₁.2
  have h₇ : x - p ≥ 0 := sub_nonneg.mpr h₅
  have h₈ : x - 15 ≤ 0 := by linarith
  have h₉ : x - p - 15 < 0 := by linarith
  rw [h₂]
  simp [abs_of_nonneg h₇, abs_of_nonpos h₈, abs_of_neg h₉]
  linarith
