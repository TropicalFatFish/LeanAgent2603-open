import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_5
  (n : ℕ)
  (h₀ : 10 ≤ n)
  (h₁ : ∃ x, x^2 = n)
  (h₂ : ∃ t, t^3 = n) :
  64 ≤ n := by
  by_contra h
  have : n < 64 := by
    omega
  interval_cases n <;> norm_num at h₁ h₂ h₀ <;>
    (try { rcases h₁ with ⟨x, hx⟩ }) <;>
    (try { rcases h₂ with ⟨t, ht⟩ }) <;>
    (try { contradiction })
