import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_229 :
  (5^30) % 7 = 1 := by
  have h : 5^6 % 7 = 1 := by norm_num
  calc
    (5^30) % 7 = ((5^6)^5) % 7 := by
      rw [show (5^30) = (5^6)^5 by rw [← pow_mul, (show 30 = 6 * 5 by norm_num)]]
    _ = (((5^6) % 7)^5) % 7 := by
      simpa [pow_mod] using congrArg (· % 7) (show (5^6 : ℕ) ^ 5 = 5^30 by rw [pow_mul, show 30 = 6 * 5 by norm_num])
    _ = (1^5) % 7 := by rw [h]
    _ = 1 := by norm_num
