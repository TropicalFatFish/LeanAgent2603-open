import Mathlib

open Nat

def sumOfDigits (n : ℕ) : ℕ := (Nat.digits 10 n).sum

theorem aime_all_2015_II_3 :
    IsLeast {m | 0 < m ∧ 17 ∣ m ∧ sumOfDigits m = 17} 476 := by
  constructor
  · constructor
    · norm_num
    · norm_num [sumOfDigits]
  · intro m hm
    rcases hm with ⟨h₁, h₂, h₃⟩
    have : ∃ k, m = 17 * k := by omega
    rcases this with ⟨k, hk⟩
    subst m
    have : k < 28 ∨ k ≥ 28 := by omega
    rcases this with hk_lt_28 | hk_ge_28
    ·
      have : 17 * k < 476 := by
        nlinarith
      interval_cases k <;> norm_num [sumOfDigits] at h₃ <;> omega
    ·
      linarith
