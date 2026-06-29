import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem imo_1959_p1
  (n : ℕ)
  (h₀ : 0 < n) :
  Nat.gcd (21*n + 4) (14*n + 3) = 1 := by
  have h₁ : (21*n + 4).gcd (14*n + 3) ∣ (21*n + 4) := Nat.gcd_dvd_left _ _
  have h₂ : (21*n + 4).gcd (14*n + 3) ∣ (14*n + 3) := Nat.gcd_dvd_right _ _
  have h₃ : 3 * (14*n + 3) = 42*n + 9 := by ring
  have h₄ : 2 * (21*n + 4) = 42*n + 8 := by ring
  have h₅ : 3 * (14*n + 3) - 2 * (21*n + 4) = 1 := by
    rw [h₃, h₄]
    omega
  have h₆ : (21*n + 4).gcd (14*n + 3) ∣ 3 * (14*n + 3) := dvd_mul_of_dvd_right h₂ 3
  have h₇ : (21*n + 4).gcd (14*n + 3) ∣ 2 * (21*n + 4) := dvd_mul_of_dvd_right h₁ 2
  have h₈ : (21*n + 4).gcd (14*n + 3) ∣ 3 * (14*n + 3) - 2 * (21*n + 4) := Nat.dvd_sub h₆ h₇
  rw [h₅] at *
  exact Nat.dvd_one.mp h₈
