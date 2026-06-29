import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_222
  (b : ℕ)
  (h₀ : Nat.lcm 120 b = 3720)
  (h₁ : Nat.gcd 120 b = 8) :
  b = 248 := by
  have h₂ : Nat.lcm 120 b * Nat.gcd 120 b = 120 * b := Nat.lcm_mul_gcd 120 b
  rw [h₀, h₁] at h₂
  norm_num at h₂ ⊢
  omega
