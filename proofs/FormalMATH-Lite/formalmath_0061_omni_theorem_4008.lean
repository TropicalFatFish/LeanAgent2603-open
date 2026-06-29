import Mathlib

open Real Set
open scoped BigOperators

theorem omni_theorem_4008 :
  IsLeast {t : ℝ | ∃ x y : ℝ, x > 0 ∧ y > 0 ∧ x + y ≤ 1 ∧ t = x ^ 4 + y ^ 4 - x ^ 2 * y - x * y ^ 2} (-1/8) := by
  constructor
  ·
    use 1/2, 1/2
    norm_num
  ·
    intro t h
    rcases h with ⟨x, y, hx, hy, hxy, rfl⟩
    have h₁ : 0 < x * y := mul_pos hx hy
    have h₂ : 0 < x + y := add_pos (by linarith) hy
    have h₃ : (x + y) ^ 2 ≤ 1 := by
      nlinarith
    have h₄ : 0 < x ^ 3 := pow_pos hx 3
    have h₅ : 0 < y ^ 3 := pow_pos hy 3
    nlinarith [sq_nonneg (x - y), mul_self_nonneg (x - 1/2), mul_self_nonneg (y - 1/2),
      mul_self_nonneg (x ^ 2 - y ^ 2), mul_self_nonneg (x + y - 1),
      mul_nonneg hx.le hy.le, mul_nonneg hx.le (sub_nonneg.mpr h₃)]
