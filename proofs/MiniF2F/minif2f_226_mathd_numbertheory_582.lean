import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_582
  (n : ℕ)
  (h₀ : 0 < n)
  (h₁ : 3∣n) :
  ((n + 4) + (n + 6) + (n + 8)) % 9 = 0 := by
  cases' h₁ with k hk
  have h₃ : ((n + 4) + (n + 6) + (n + 8)) = 3 * n + 18 := by
    rw [hk]
    ring
  have h₄ : 9 ∣ 3 * n + 18 := by
    have h₅ : 3 * n = 9 * k := by
      calc
        3 * n = 3 * (3 * k) := by rw [hk]
        _ = 9 * k := by ring
    rw [h₅]
    exact dvd_mul_right 9 (k + 2)
  rw [h₃] at *
  exact Nat.mod_eq_zero_of_dvd h₄
