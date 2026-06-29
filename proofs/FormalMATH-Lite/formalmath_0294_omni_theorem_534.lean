import Mathlib

open Nat BigOperators

theorem omni_theorem_534 :
    IsLeast {n | (Nat.digits 10 n).length = 5 ∧ List.Palindrome (Nat.digits 10 n) ∧ 99 ∣ n} 54945 := by
  native_decide
