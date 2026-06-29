import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_17
  (a : ℝ)
  (h₀ : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) + Real.sqrt (1 + Real.sqrt (1 + a)) = 6) :
  a = 8 := by

  have h₁ : 0 ≤ 1 + a := by
    by_contra h

    have h₂ : 1 + a < 0 := by linarith
    have h₃ : Real.sqrt (1 + a) = 0 :=
      by
        rw [Real.sqrt_eq_zero_of_nonpos]
        <;> linarith

    have h₄ : Real.sqrt (16 + 16 * a) = 0 :=
      by
        rw [Real.sqrt_eq_zero_of_nonpos]
        <;> linarith
    have h₅ : Real.sqrt (1 + Real.sqrt (1 + a)) = 1 := by
      rw [h₃]
      norm_num
    have h₆ : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) = 2 := by
      rw [h₄]
      norm_num

    have h₇ : (2 : ℝ) + 1 = 6 := by
      linarith [h₅, h₆]
    linarith [h₇]

  have h₂ : Real.sqrt (16 + 16 * a) = 4 * Real.sqrt (1 + a) := by
    have h₃ : 0 ≤ 1 + a := h₁
    have h₄ : 16 + 16 * a = 16 * (1 + a) := by ring
    rw [h₄]
    rw [Real.sqrt_mul] <;> norm_num <;> linarith

  rw [h₂] at h₀

  have h₃ : Real.sqrt (4 + 4 * Real.sqrt (1 + a)) = 2 * Real.sqrt (1 + Real.sqrt (1 + a)) := by
    have h₄ : 0 ≤ Real.sqrt (1 + a) := Real.sqrt_nonneg (1 + a)
    have h₅ : 0 ≤ 1 + Real.sqrt (1 + a) := by linarith
    have h₆ : 4 + 4 * Real.sqrt (1 + a) = 4 * (1 + Real.sqrt (1 + a)) := by ring
    rw [h₆]
    rw [Real.sqrt_mul] <;> norm_num <;> linarith

  rw [h₃] at h₀

  have h₄ : 3 * Real.sqrt (1 + Real.sqrt (1 + a)) = 6 := by linarith

  have h₅ : Real.sqrt (1 + Real.sqrt (1 + a)) = 2 := by
    norm_num at h₄
    linarith

  have h₆ : 1 + Real.sqrt (1 + a) = 4 := by
    have h₇ : 0 ≤ 1 + Real.sqrt (1 + a) := by
      apply add_nonneg
      · linarith
      · linarith [Real.sqrt_nonneg (1 + a)]
    have h₈ : (Real.sqrt (1 + Real.sqrt (1 + a))) ^ 2 = 4 := by
      rw [h₅]
      norm_num
    have h₉ : 1 + Real.sqrt (1 + a) = 4 := by
      have h₁₀ : (Real.sqrt (1 + Real.sqrt (1 + a))) ^ 2 = 1 + Real.sqrt (1 + a) := by
        apply sq_sqrt
        linarith
      rw [h₁₀] at h₈
      linarith
    exact h₉

  have h₇ : Real.sqrt (1 + a) = 3 := by linarith

  have h₈ : 1 + a = 9 := by
    have h₉ : 0 ≤ 1 + a := by linarith
    have h₁₀ : (Real.sqrt (1 + a)) ^ 2 = 1 + a := by
      apply sq_sqrt
      linarith
    rw [h₇] at h₁₀
    norm_num at h₁₀
    linarith

  linarith
