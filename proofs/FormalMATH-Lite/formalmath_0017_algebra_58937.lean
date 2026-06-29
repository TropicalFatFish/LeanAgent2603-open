import Mathlib

theorem algebra_58937 {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0) :
    Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1 := by

  simp [pow_succ, Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib, Nat.add_sub_add_right]
  <;> ring_nf
  <;> omega
