import Mathlib

open Finset

theorem omni_theorem_388 : (2^2001) % (2^7 - 1) = 64 := by
  have h1 : (2^7 : ℕ) - 1 = 127 := by norm_num
  have h_mod : (2 : ℕ) ^ 7 % 127 = 1 := by norm_num
  have : (2 : ℕ) ^ 2001 % 127 = 64 := by
    have : 2001 = 7 * 285 + 6 := by norm_num
    rw [this]
    simp [pow_add, pow_mul, h_mod, pow_pos]
    <;> norm_num
    <;> omega
  rw [← this]
  congr 1
  <;> norm_num
  <;> linarith
