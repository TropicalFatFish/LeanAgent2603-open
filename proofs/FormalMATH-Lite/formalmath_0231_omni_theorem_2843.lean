import Mathlib

def s : ℕ → ℕ
| n => (Nat.digits 10 n).sum

open Finset

theorem omni_theorem_2843 :
    ((Icc 100 999).filter (fun n => 7 ≤ s n ∧ s n ≤ 11)).card % 100 = 24 := by
  native_decide
