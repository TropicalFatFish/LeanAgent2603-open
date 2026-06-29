import Mathlib

open Real Set
open scoped BigOperators

theorem quantitative_reasoning_zh_blue_880 :
  IsGreatest {t : ℝ | ∃ x y z : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ x + y + z = 1 ∧ t = x^2 * y + y^2 * z + z^2 * x} (4 / 27) ∧
  IsLeast {t : ℝ | ∃ x y z : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ x + y + z = 1 ∧ t = x^2 * y + y^2 * z + z^2 * x} 0 := by
  constructor
  · constructor
    · refine ⟨2 / 3, 1 / 3, 0, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num
    · intro t ht
      rcases ht with ⟨x, y, z, hx, hy, hz, hsum, ht⟩
      rw [ht]
      have hx0 : 0 ≤ x := hx
      have hy0 : 0 ≤ y := hy
      have hz0 : 0 ≤ z := hz
      have hsos :
          0 ≤
            x * (-2 * x + 4 * y + z) ^ 2 +
              y * (-2 * y + 4 * z + x) ^ 2 +
              z * (-2 * z + 4 * x + y) ^ 2 := by
        have hxterm : 0 ≤ x * (-2 * x + 4 * y + z) ^ 2 :=
          mul_nonneg hx0 (sq_nonneg _)
        have hyterm : 0 ≤ y * (-2 * y + 4 * z + x) ^ 2 :=
          mul_nonneg hy0 (sq_nonneg _)
        have hzterm : 0 ≤ z * (-2 * z + 4 * x + y) ^ 2 :=
          mul_nonneg hz0 (sq_nonneg _)
        nlinarith
      have hid :
          x * (-2 * x + 4 * y + z) ^ 2 +
              y * (-2 * y + 4 * z + x) ^ 2 +
              z * (-2 * z + 4 * x + y) ^ 2 =
            4 * (x + y + z) ^ 3 - 27 * (x ^ 2 * y + y ^ 2 * z + z ^ 2 * x) := by
        ring
      have hbound : 0 ≤ 4 * (x + y + z) ^ 3 - 27 * (x ^ 2 * y + y ^ 2 * z + z ^ 2 * x) := by
        rwa [← hid]
      nlinarith
  · constructor
    · refine ⟨1, 0, 0, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num
    · intro t ht
      rcases ht with ⟨x, y, z, hx, hy, hz, hsum, ht⟩
      rw [ht]
      have hx0 : 0 ≤ x := hx
      have hy0 : 0 ≤ y := hy
      have hz0 : 0 ≤ z := hz
      have hxy : 0 ≤ x ^ 2 * y := mul_nonneg (sq_nonneg x) hy0
      have hyz : 0 ≤ y ^ 2 * z := mul_nonneg (sq_nonneg y) hz0
      have hzx : 0 ≤ z ^ 2 * x := mul_nonneg (sq_nonneg z) hx0
      nlinarith
