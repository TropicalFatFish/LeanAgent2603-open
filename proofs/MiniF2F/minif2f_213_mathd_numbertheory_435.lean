import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_435
  (k : ℕ)
  (h₀ : 0 < k)
  (h₁ : ∀ n, Nat.gcd (6 * n + k) (6 * n + 3) = 1)
  (h₂ : ∀ n, Nat.gcd (6 * n + k) (6 * n + 2) = 1)
  (h₃ : ∀ n, Nat.gcd (6 * n + k) (6 * n + 1) = 1) :
  5 ≤ k := by
  by_contra h
  have h₄ : k ≤ 4 := by linarith
  have h₅ : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
    omega
  rcases h₅ with (hk1 | hk2 | hk3 | hk4)
  ·
    have := h₃ 1
    simp [hk1, Nat.succ_eq_add_one] at this
    <;> norm_num at this
    <;> contradiction
  ·
    have := h₂ 0
    simp [hk2] at this
    <;> norm_num at this
    <;> contradiction
  ·
    have := h₁ 0
    simp [hk3] at this
    <;> norm_num at this
    <;> contradiction
  ·
    have := h₂ 0
    simp [hk4] at this
    <;> norm_num at this
    <;> contradiction
