import Mathlib

open Finset

theorem omni_theorem_446 :
    IsLeast {n | 0 < n ∧ 100 ∣ ∑ i ∈ Icc 1 n, i^2} 24 := by
  constructor
  · constructor
    · norm_num
    · norm_num [Finset.sum_Icc_succ_top]
  · rintro n ⟨hn, hdiv⟩
    by_contra h
    interval_cases n <;> norm_num [Finset.sum_Icc_succ_top] at hdiv
    <;> decide
