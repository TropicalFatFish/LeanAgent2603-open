import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_247
  (n : ℕ)
  (h₀ : (3 * n) % 11 = 2) :
  n % 11 = 8 := by
  have h₁ : n % 11 < 11 := Nat.mod_lt n (by norm_num)
  have h₂ : n % 11 ≥ 0 := Nat.zero_le (n % 11)
  have : n % 11 = 0 ∨ n % 11 = 1 ∨ n % 11 = 2 ∨ n % 11 = 3 ∨
          n % 11 = 4 ∨ n % 11 = 5 ∨ n % 11 = 6 ∨ n % 11 = 7 ∨
          n % 11 = 8 ∨ n % 11 = 9 ∨ n % 11 = 10 := by
    omega
  rcases this with (h | h | h | h | h | h | h | h | h | h | h) <;>
    (try { simp_all [Nat.mul_mod, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt] }) <;>
    (try { omega }) <;>
    (try { linarith })
