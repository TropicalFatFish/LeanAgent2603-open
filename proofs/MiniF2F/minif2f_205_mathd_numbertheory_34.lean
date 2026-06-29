import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_34
  (x: ℕ)
  (h₀ : x < 100)
  (h₁ : x*9 % 100 = 1) :
  x = 89 := by
  have h₂ : x * 9 = 100 * (x * 9 / 100) + 1 := by
    have := Nat.mod_add_div (x * 9) 100
    rw [Nat.add_comm] at this
    rw [h₁] at this
    omega
  have h₃ : ∃ k : ℕ, x * 9 = 100 * k + 1 := by
    use x * 9 / 100
  have h₄ : x = 89 := by
    cases' h₃ with k hk
    omega
  exact h₄
