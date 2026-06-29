import Mathlib

open Real Set
open scoped BigOperators

theorem omni_theorem_1154 :
  IsLeast {z : ℝ | ∃ x y : ℝ, z = max (max (x * y) (1 - x - y + x * y)) (x + y - 2 * x * y) ∧ 0 ≤ x ∧ x ≤ y ∧ y ≤ 1} (4 / 9) := by
  constructor
  ·
    use 2 / 3, 2 / 3
    norm_num [max_eq_right, max_eq_left]
    <;> linarith
  ·
    intro z hz
    rcases hz with ⟨x, y, rfl, hx0, hxy, hyl1⟩
    have h1 : x * y + (1 - x - y + x * y) + (x + y - 2 * x * y) = 1 := by ring
    have h2 : max (max (x * y) (1 - x - y + x * y)) (x + y - 2 * x * y) ≥ 4 / 9 := by
      cases' le_total (x * y) (1 - x - y + x * y) with h h <;>
        cases' le_total (1 - x - y + x * y) (x + y - 2 * x * y) with h' h' <;>
          cases' le_total (x * y) (x + y - 2 * x * y) with h'' h'' <;>
            simp_all [max_eq_left, max_eq_right] <;>
              nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hyl1),
                mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hyl1)]
    linarith
