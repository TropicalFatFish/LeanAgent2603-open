import Mathlib

theorem aime_all_1988_9 :
    IsLeast {n : ℕ | n > 0 ∧ (n^3) % 1000 = 888} 192 := by
  constructor
  ·
    norm_num
  ·
    intro n hn
    rcases hn with ⟨hn_pos, h_cube⟩
    have : 192 ≤ n := by
      by_contra h
      have h_lt : n < 192 := by omega
      have h_pos : n > 0 := hn_pos
      interval_cases n <;>
        (try { contradiction }) <;>
        (try {
          simp [h_pos, h_lt, h_cube] at this
          norm_num [pow_succ, Nat.mul_mod, Nat.add_mod] at this ⊢
          omega
        })
    exact this
