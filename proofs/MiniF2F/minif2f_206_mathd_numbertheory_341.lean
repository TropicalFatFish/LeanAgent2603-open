import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_341
  (a b c : ℕ)
  (h₀ : a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9)
  (h₁ : Nat.digits 10 ((5^100) % 1000) = [c,b,a]) :
  a + b + c = 13 := by
  have h₂ : (5^100) % 1000 = 625 := by norm_num
  rw [h₂] at h₁
  have h₃ : Nat.digits 10 625 = [5, 2, 6] := by norm_num
  rw [h₃] at h₁
  rcases h₁ with h₁
  simp at h₁
  linarith
