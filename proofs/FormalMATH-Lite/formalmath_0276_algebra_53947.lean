import Mathlib

open Nat

theorem algebra_53947 {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n) := by
  exact (Nat.fib_gcd m n).symm
