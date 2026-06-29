import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem numbertheory_2pownm1prime_nprime
  (n : ℕ)
  (h₀ : 0 < n)
  (h₁ : Nat.Prime (2^n - 1)) :
  Nat.Prime n := by
  by_cases hn : n = 1
  · subst n
    norm_num at h₁
  · exact (Nat.prime_of_pow_sub_one_prime (a := 2) (n := n) hn h₁).2
