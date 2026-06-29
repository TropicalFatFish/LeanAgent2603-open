import Mathlib

theorem u_math_243 (x : ℝ) :
    abs (x^2 + 4 * x + 9 + 2 * x - 3) = abs (x^2 + 4 * x + 9) + abs (2 * x - 3) ↔
    3 / 2 ≤ x := by
  constructor
  · intro h
    by_contra hx
    have hbneg : 2 * x - 3 < 0 := by linarith
    have hApos : 0 < x ^ 2 + 4 * x + 9 := by
      nlinarith [sq_nonneg (x + 2)]
    have hAbsA : abs (x ^ 2 + 4 * x + 9) = x ^ 2 + 4 * x + 9 := abs_of_pos hApos
    have hAbsB : abs (2 * x - 3) = -(2 * x - 3) := abs_of_neg hbneg
    by_cases hsum : 0 ≤ x ^ 2 + 4 * x + 9 + 2 * x - 3
    · have hAbsSum : abs (x ^ 2 + 4 * x + 9 + 2 * x - 3) =
          x ^ 2 + 4 * x + 9 + 2 * x - 3 := abs_of_nonneg hsum
      rw [hAbsSum, hAbsA, hAbsB] at h
      linarith
    · have hsumneg : x ^ 2 + 4 * x + 9 + 2 * x - 3 < 0 := by linarith
      have hAbsSum : abs (x ^ 2 + 4 * x + 9 + 2 * x - 3) =
          -(x ^ 2 + 4 * x + 9 + 2 * x - 3) := abs_of_neg hsumneg
      rw [hAbsSum, hAbsA, hAbsB] at h
      nlinarith
  · intro hx
    have hb : 0 ≤ 2 * x - 3 := by linarith
    have hA : 0 ≤ x ^ 2 + 4 * x + 9 := by
      nlinarith [sq_nonneg (x + 2)]
    have hsum : 0 ≤ x ^ 2 + 4 * x + 9 + 2 * x - 3 := by linarith
    rw [abs_of_nonneg hsum, abs_of_nonneg hA, abs_of_nonneg hb]
    ring
