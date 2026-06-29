import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem induction_pprime_pdvdapowpma
  (p a : ℕ)
  (h₀ : 0 < a)
  (h₁ : Nat.Prime p) :
  p ∣ (a^p - a) := by
  letI : Fact p.Prime := ⟨h₁⟩
  have hle : a ≤ a ^ p := by
    exact le_self_pow (Nat.succ_le_of_lt h₀) h₁.ne_zero
  apply (ZMod.natCast_zmod_eq_zero_iff_dvd (a ^ p - a) p).mp
  rw [Nat.cast_sub hle, Nat.cast_pow]
  change ((a : ZMod p) ^ p - (a : ZMod p) = 0)
  rw [ZMod.pow_card]
  ring
