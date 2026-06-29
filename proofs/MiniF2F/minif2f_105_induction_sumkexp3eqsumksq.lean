import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem induction_sumkexp3eqsumksq
  (n : ℕ) :
  ∑ k ∈ Finset.range n, k^3 = (∑ k ∈ Finset.range n, k)^2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    set S := ∑ k ∈ Finset.range n, k
    cases n with
    | zero => simp [S]
    | succ m =>
      have hsNat : S * 2 = (m + 1) * m := by
        simpa [S, Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          Finset.sum_range_id_mul_two (m + 1)
      have hs : (2 : ℤ) * (S : ℤ) = ((m : ℤ) + 1) * (m : ℤ) := by
        have hs0 : (S : ℤ) * 2 = ((m + 1 : ℕ) : ℤ) * (m : ℤ) := by
          exact_mod_cast hsNat
        norm_num [Nat.cast_add, Nat.cast_one] at hs0 ⊢
        linarith
      have hz : (S : ℤ) ^ 2 + (((m : ℤ) + 1) ^ 3) = ((S : ℤ) + ((m : ℤ) + 1)) ^ 2 := by
        nlinarith
      have hz' : (S : ℤ) ^ 2 + (((m + 1 : ℕ) : ℤ) ^ 3) = ((S : ℤ) + ((m + 1 : ℕ) : ℤ)) ^ 2 := by
        norm_num [Nat.cast_add, Nat.cast_one]
        exact hz
      exact_mod_cast hz'
