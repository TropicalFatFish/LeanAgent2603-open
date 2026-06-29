import Mathlib

theorem algebra_58649 (f : ℚ → ℤ) :
    ∃ a b, a ≤ b ∧ f a + f b ≤ 2 * f ((a + b) / 2) := by
  use 0, 0
  constructor
  · norm_num
  · ring_nf
    <;> linarith
