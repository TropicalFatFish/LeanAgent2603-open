import Mathlib

def a (n : ℕ) := 500 + (n - 1) * 500

theorem omni_theorem_3420 :
    ∃ n, a n = 4500 ∧ n % 7 = 2 := by
  use 9
  constructor
  · norm_num [a]
  · norm_num
