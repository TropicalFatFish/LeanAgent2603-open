import Mathlib

open Real Set
open scoped BigOperators

theorem quantitative_reasoning_zh_blue_501 :
  IsLeast {u : ℝ | ∃ x y : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ 3 ≤ x + y ∧ x + y ≤ 5 ∧ u = x^2 - x * y + y^2} (9 / 4) ∧
  IsGreatest {u : ℝ | ∃ x y : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ 3 ≤ x + y ∧ x + y ≤ 5 ∧ u = x^2 - x * y + y^2} 25 := by
  constructor
  constructor
  · use 3 / 2, 3 / 2
    norm_num
  · intro u hu
    rcases hu with ⟨x, y, hx, hy, hsum_lo, hsum_hi, heq⟩
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 3)]
  constructor
  · use 5, 0
    norm_num
  · intro u hu
    rcases hu with ⟨x, y, hx, hy, hsum_lo, hsum_hi, heq⟩
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 5)]
