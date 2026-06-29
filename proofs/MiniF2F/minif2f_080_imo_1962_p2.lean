import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem imo_1962_p2
  (x : ℝ)
  (h₀ : 0 ≤ 3 - x)
  (h₁ : 0 ≤ x + 1)
  (h₂ : 1 / 2 < Real.sqrt (3 - x) - Real.sqrt (x + 1)) :
  -1 ≤ x ∧ x < 1 - Real.sqrt 31 / 8 := by
  have h3 : -1 ≤ x := by

    linarith
  have h4 : x < 1 - Real.sqrt 31 / 8 := by

    have h5 : 0 ≤ Real.sqrt (x + 1) := by
      apply Real.sqrt_nonneg
    have h6 : 0 ≤ Real.sqrt (3 - x) := by
      apply Real.sqrt_nonneg

    have h7 : Real.sqrt (3 - x) > Real.sqrt (x + 1) + 1 / 2 := by
      linarith

    have h8 : 8 * (Real.sqrt (x + 1))^2 + 4 * Real.sqrt (x + 1) - 15 < 0 := by
      nlinarith [h5, h6,
        Real.sq_sqrt (by linarith : 0 ≤ x + 1),
        Real.sq_sqrt (by linarith : 0 ≤ 3 - x),
        sq_nonneg (Real.sqrt (3 - x) - Real.sqrt (x + 1))]
    have h9 : Real.sqrt (x + 1) < 5 / 4 := by
      nlinarith [sq_nonneg (4 * Real.sqrt (x + 1) - 5)]

    have h10 : x < 1 - Real.sqrt 31 / 8 := by
      have h11 : (Real.sqrt (x + 1))^2 = x + 1 := by
        rw [Real.sq_sqrt (by linarith)]
      have h12 : 0 ≤ 5 / 8 := by norm_num
      nlinarith [Real.sqrt_nonneg 31, Real.sqrt_nonneg (x + 1),
        h12, h9, h5, h6, h11,
        Real.sq_sqrt (show 0 ≤ 31 from by norm_num)]
    exact h10
  exact ⟨h3, h4⟩
