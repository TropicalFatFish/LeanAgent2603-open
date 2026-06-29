import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_559
  (x y : ℕ)
  (h₀ : x % 3 = 2)
  (h₁ : y % 5 = 4)
  (h₂ : x % 10 = y % 10) :
  14 ≤ x := by
  have h₃ : x % 10 = 4 ∨ x % 10 = 9 := by
    have h₄ : y % 10 = 4 ∨ y % 10 = 9 := by
      norm_num [Nat.mod_eq_of_lt] at h₁
      omega
    omega

  cases h₃ with
  | inl h₃ =>
    have h₄ : x % 10 = 4 := h₃
    have h₅ : x ≥ 14 := by
      by_contra h
      have h₆ : x < 14 := lt_of_not_ge h
      interval_cases x <;> norm_num [h₀, h₆] at *
    omega
  | inr h₃ =>
    have h₄ : x % 10 = 9 := h₃
    have h₅ : x ≥ 14 := by
      by_contra h
      have h₆ : x < 14 := lt_of_not_ge h
      interval_cases x <;> norm_num [h₀, h₆] at *
    omega
