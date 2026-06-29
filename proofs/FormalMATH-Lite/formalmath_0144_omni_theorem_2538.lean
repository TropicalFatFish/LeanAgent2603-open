import Mathlib

open Nat

def sumOfDigits (b : ℕ) (n : ℕ) := (Nat.digits b n).sum

theorem omni_theorem_2538 :
    IsLeast {n | 10 < n ∧ sumOfDigits 17 n = sumOfDigits 10 n} 153 := by
  unfold IsLeast
  constructor
  · constructor
    · norm_num
    · norm_num [sumOfDigits]
  · intro m hm
    simp only [Set.mem_setOf_eq] at hm
    rcases lt_or_ge m 153 with hge | hge_lt
    · have : 10 < m := by linarith
      interval_cases m <;> simp_all [sumOfDigits]
    · apply hge_lt
