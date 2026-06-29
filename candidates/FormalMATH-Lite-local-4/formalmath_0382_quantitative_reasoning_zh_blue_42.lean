import Mathlib

open Finset

theorem quantitative_reasoning_zh_blue_42 {n : ℕ} (hn : 0 < n) :
    {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1 := by
  apply eq_of_subset_of_superset
  <;> simp_all
  <;> apply Filter.tendsto_atTop_atTop_nhds
  <;> norm_num
  <;> linarith
