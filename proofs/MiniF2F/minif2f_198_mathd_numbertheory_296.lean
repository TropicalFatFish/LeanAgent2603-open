import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_296
  (n : ℕ)
  (h₀ : 2 ≤ n)
  (h₁ : ∃ x, x^3 = n)
  (h₂ : ∃ t, t^4 = n) :
  4096 ≤ n := by
  obtain ⟨x, hx⟩ := h₁
  obtain ⟨t, ht⟩ := h₂
  by_contra h
  have hnlt : n < 4096 := Nat.lt_of_not_ge h
  have hxlt : x < 16 := by
    by_contra hxge
    have hxge' : 16 ≤ x := by omega
    have hp : 16 ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left hxge' 3
    rw [hx] at hp
    norm_num at hp
    omega
  have htlt : t < 8 := by
    by_contra htge
    have htge' : 8 ≤ t := by omega
    have hp : 8 ^ 4 ≤ t ^ 4 := Nat.pow_le_pow_left htge' 4
    rw [ht] at hp
    norm_num at hp
    omega
  interval_cases x <;> interval_cases t <;> norm_num at hx ht h₀ <;> omega
