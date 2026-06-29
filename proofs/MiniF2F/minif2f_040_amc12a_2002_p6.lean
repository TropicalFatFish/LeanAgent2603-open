import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem amc12a_2002_p6
  (n : ℕ)
  (h₀ : 0 < n) :
  ∃ m, (m > n ∧ ∃ p, m * p ≤ m + p) := by
  use n + 1
  constructor
  · exact Nat.lt_succ_self n
  refine ⟨1, ?_⟩
  ring
  linarith
