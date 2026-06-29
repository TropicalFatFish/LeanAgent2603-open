import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_185
  (n : ℕ)
  (h₀ : n % 5 = 3) :
  (2 * n) % 5 = 1 := by
  calc
    (2 * n) % 5 = ((2 % 5) * (n % 5)) % 5 := by rw [Nat.mul_mod]
    _ = (2 * (n % 5)) % 5 := by
      rw [show 2 % 5 = 2 by norm_num]
    _ = (2 * 3) % 5 := by rw [h₀]
    _ = 6 % 5 := by norm_num
    _ = 1 := by norm_num
