import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem induction_nfactltnexpnm1ngt3
  (n : ℕ)
  (h₀ : 3 ≤ n) :
  (n)! < n^(n - 1) := by
  induction' n with n ih
  · omega
  cases n with
  | zero => norm_num at h₀
  | succ n =>
    by_cases hn : 3 ≤ n.succ
    · have ih' : n.succ ! < n.succ ^ (n.succ - 1) := ih hn
      calc
        (n.succ.succ)! = n.succ.succ * n.succ ! := by rw [Nat.factorial_succ]
        _ < n.succ.succ * n.succ ^ (n.succ - 1) := by exact Nat.mul_lt_mul_of_pos_left ih' (Nat.succ_pos _)
        _ ≤ n.succ.succ * n.succ.succ ^ (n.succ - 1) := by
          gcongr
          omega
        _ = n.succ.succ ^ (n.succ.succ - 1) := by
          have hsub1 : n.succ - 1 = n := by omega
          have hsub2 : n.succ.succ - 1 = n.succ := by omega
          rw [hsub1, hsub2, Nat.pow_succ']
    · have hnle : n ≤ 1 := by omega
      interval_cases n
      · norm_num at h₀
      · norm_num
