import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem numbertheory_3pow2pownm1mod2pownp3eq2pownp2
  (n : ℕ)
  (h₀ : 0 < n) :
  (3^(2^n) - 1) % (2^(n + 3)) = 2^(n + 2) := by
  have hstrong :
      ∀ m : ℕ, ∃ q : ℕ,
        3 ^ (2 ^ (m + 1)) = 1 + 2 ^ (m + 3) * (2 * q + 1) := by
    intro m
    induction' m with m ih
    · use 0
      norm_num
    · rcases ih with ⟨q, hq⟩
      use q + 2 ^ (m + 1) * (2 * q + 1) ^ 2
      have hpow :
          3 ^ (2 ^ (m + 1 + 1)) = (3 ^ (2 ^ (m + 1))) ^ 2 := by
        have htwo : 2 ^ (m + 1 + 1) = 2 ^ (m + 1) * 2 := by
          rw [show m + 1 + 1 = (m + 1) + 1 by omega, pow_succ]
        rw [htwo, pow_mul]
      rw [hpow, hq]
      ring_nf
  cases n with
  | zero =>
      omega
  | succ m =>
      rcases hstrong m with ⟨q, hq⟩
      rw [hq]
      have hlt : 2 ^ (m + 3) < 2 ^ (m + 4) := by
        apply Nat.pow_lt_pow_right
        · norm_num
        · omega
      have hrewrite :
          1 + 2 ^ (m + 3) * (2 * q + 1) - 1 =
            2 ^ (m + 3) + q * 2 ^ (m + 4) := by
        have hsucc : 2 ^ (m + 4) = 2 * 2 ^ (m + 3) := by
          rw [show m + 4 = (m + 3) + 1 by omega, pow_succ]
          ring
        rw [hsucc]
        ring_nf
        omega
      rw [hrewrite]
      have hmod :
          (2 ^ (m + 3) + q * 2 ^ (m + 4)) % 2 ^ (m + 4) = 2 ^ (m + 3) := by
        rw [mul_comm q (2 ^ (m + 4))]
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
      simpa [Nat.add_assoc] using hmod
