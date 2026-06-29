import Mathlib

open Nat

def is_nine_representable (n : ℕ) : Prop :=
  ∃ a b c, n = 100 * a + 10 * b + c ∧ a < 9 ∧ b < 9 ∧ c < 9 ∧
  n = 81 * b + 9 * c + a

theorem aime_all_2022_I_2 : {n | n ∈ Finset.Icc 100 999 ∧ is_nine_representable n} = {227} := by
  ext n
  simp [is_nine_representable] at *
  constructor
  · intro hn
    rcases hn with ⟨conj_1, conj_2⟩
    rcases conj_1 with ⟨h100, h999⟩
    rcases conj_2 with ⟨a, b, c, h_eq1, ha, hb, hc, h_eq2⟩
    have h4 : 100 * a + 10 * b + c = 81 * b + 9 * c + a := by omega
    have h5 : 99 * a = 71 * b + 8 * c := by omega
    have ha' : a >= 1 := by omega
    interval_cases a <;> norm_num at h5 h4 ⊢ <;>
      (try omega) <;>
      (try
        { cases b <;> norm_num at * <;>
          (try omega) <;>
          (try
            { cases c <;> omega })
      })
  · rintro rfl
    constructor
    · omega
    · use 2, 2, 7
      <;> simp_all
      <;> omega
