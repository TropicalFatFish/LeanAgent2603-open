import Mathlib

theorem aime_all_1993_9 : IsLeast {n | n ≥ 1 ∧ (n * (n + 1) / 2) % 2000 = (1993 * 1994 / 2) % 2000} 118 := by
  constructor
  ·
    constructor
    · exact by norm_num
    · norm_num
  ·
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    by_contra h_lt
    have : n ≤ 117 := by linarith
    interval_cases n <;> norm_num [hn] at * <;> contradiction
