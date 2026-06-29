import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem amc12_2000_p6
  (p q : ℕ)
  (h₀ : Nat.Prime p ∧ Nat.Prime q)
  (h₁ : 4 ≤ p ∧ p ≤ 18)
  (h₂ : 4 ≤ q ∧ q ≤ 18) :
  p * q - (p + q) ≠ 194 := by
  intro hi
  rcases h₁ with ⟨h₁_left, h₁_right⟩
  rcases h₂ with ⟨h₂_left, h₂_right⟩
  interval_cases p <;> interval_cases q <;>
    norm_num [hi] at *
