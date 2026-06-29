import Mathlib

open Real Set
open scoped BigOperators

theorem quantitative_reasoning_zh_blue_333 (a : ℝ) (ha : 1 ≤ a) :
    IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2) := by
  constructor
  ·
    use 0, 0, a
    constructor
    ·
      norm_num
    · constructor
      ·
        norm_num
      · constructor
        ·
          linarith
        ·
          constructor
          · norm_num
          · ring
  ·
    intro t ht
    rcases ht with ⟨x, y, z, hx, hy, hz, hsum, hdef⟩
    rw [hdef] at *
    have h2 : y = a - x - z := by linarith
    rw [h2]
    have h3 : 0 ≤ x := hx
    have h4 : 0 ≤ z := hz
    have h5 : 0 ≤ a - x - z := by linarith [hy]

    nlinarith [sq_nonneg (2 * x + 3 * z - 2 * a), sq_nonneg (x - a), sq_nonneg (z - a)]
