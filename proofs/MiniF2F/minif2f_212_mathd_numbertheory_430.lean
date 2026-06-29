import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_430
  (a b c : ℕ)
  (h₀ : 1 ≤ a ∧ a ≤ 9)
  (h₁ : 1 ≤ b ∧ b ≤ 9)
  (h₂ : 1 ≤ c ∧ c ≤ 9)
  (h₃ : a ≠ b)
  (h₄ : a ≠ c)
  (h₅ : b ≠ c)
  (h₆ : a + b = c)
  (h₇ : 10 * a + a - b = 2 * c)
  (h₈ : c * b = 10 * a + a + a) :
  a + b + c = 8 := by
  rcases h₀ with ⟨ha1, ha9⟩
  rcases h₁ with ⟨hb1, hb9⟩
  rcases h₂ with ⟨hc1, hc9⟩
  have hb : b = 3 * a := by omega
  have hc : c = 4 * a := by omega
  subst b
  subst c
  have ha : a = 1 := by
    nlinarith [h₈, ha1]
  subst a
  norm_num
