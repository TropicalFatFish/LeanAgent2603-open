import Mathlib

def a (n : ℕ) := 6 ^ n + 8 ^ n

theorem aime_all_1983_6 : a 83 % 49 = 35 := by
  rw [a]
  norm_num
