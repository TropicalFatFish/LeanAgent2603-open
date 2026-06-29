import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_427
  (a : ℕ)
  (h₀ : a = (∑ k ∈ (Nat.divisors 500), k)) :
  ∑ k ∈ Finset.filter (λ x => Nat.Prime x) (Nat.divisors a), k = 25 := by
  have ha : a = 1092 := by
    rw [h₀]
    native_decide
  rw [ha]
  native_decide
