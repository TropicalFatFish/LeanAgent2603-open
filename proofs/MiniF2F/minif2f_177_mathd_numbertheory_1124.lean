import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_1124
  (n : ℕ)
  (h₀ : n ≤ 9)
  (h₁ : 18∣374 * 10 + n) :
  n = 4 := by
  have h₂ : (374 * 10 + n) % 18 = 0 := by
    rw [Nat.dvd_iff_mod_eq_zero] at h₁
    exact h₁

  have h₃ : (374 * 10) % 18 = 14 := by norm_num

  have h₄ : n % 18 = 4 := by
    omega

  interval_cases n <;> norm_num [h₄]
  <;> try omega
