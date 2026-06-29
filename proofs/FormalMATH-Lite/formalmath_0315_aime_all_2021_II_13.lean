import Mathlib

open Nat

set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

theorem aime_all_2021_II_13 :
    IsLeast {n | 0 < n ∧ (2^n + 5^n - n) % 1000 = 0} 797 := by
  constructor
  · constructor
    · norm_num
    · native_decide
  · intro n hn
    by_contra hle
    have hnlt : n < 797 := by omega
    let k : Fin 797 := ⟨n, hnlt⟩
    have hsmall :
        ∀ k : Fin 797,
          0 < (k : ℕ) →
          (2 ^ (k : ℕ) + 5 ^ (k : ℕ) - (k : ℕ)) % 1000 ≠ 0 := by
      native_decide
    exact (hsmall k hn.1) hn.2
