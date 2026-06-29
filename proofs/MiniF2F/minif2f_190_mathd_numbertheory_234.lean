import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_234
  (a b : ℕ)
  (h₀ : 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9)
  (h₁ : (10 * a + b)^3 = 912673) :
  a + b = 16 := by
  have h₂ : 10 * a + b = 97 := by
    have h₃ : (10 * a + b) ^ 3 = 912673 := h₁
    have h₄ : 10 * a + b ≥ 10 := by
      nlinarith [h₀.1]
    have h₅ : 10 * a + b ≤ 99 := by
      nlinarith [h₀.2.1, h₀.2.2]
    have h₆ : 97 ^ 3 = 912673 := by norm_num
    have : ∀ n : ℕ, n ≤ 99 → n ^ 3 = 912673 → n = 97 := by
      intro n hn h1
      interval_cases n <;> simp_all [pow_three] <;> norm_num
    exact this (10 * a + b) h₅ h₃
  have h₃ : a = 9 := by
    have h₄ : 10 * a + b = 97 := h₂
    have h₅ : b ≤ 9 := h₀.2.2
    omega
  have h₄ : b = 7 := by
    have h₅ : 10 * a + b = 97 := h₂
    have h₆ : a = 9 := h₃
    omega
  omega
