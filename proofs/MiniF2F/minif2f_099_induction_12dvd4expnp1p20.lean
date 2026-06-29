import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem induction_12dvd4expnp1p20
  (n : ℕ) :
  12 ∣ 4^(n+1) + 20 := by
  induction n with
  | zero =>
    norm_num
  | succ n ih =>
    have p : 4^(n+2) + 20 = 4 * (4^(n+1) + 20) - 60 := by
      rw [pow_succ]
      ring_nf
      <;> omega
    rw [p]
    have h₁ : 12 ∣ 4 * (4^(n+1) + 20) := by
      apply dvd_mul_of_dvd_right
      exact ih
    omega
