import Mathlib

theorem aime_all_2018_I_11 :
    IsLeast {n : ℕ | 0 < n ∧ (3^n) % (143^2) = 1} 195 := by
  constructor
  · constructor
    · norm_num
    · norm_num
  · intro n hn
    rcases hn with ⟨hn_pos, hn_mod⟩
    by_contra h_ge
    have h_lt : n < 195 := by omega
    interval_cases n <;> norm_num [pow_succ] at hn_mod
