import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem imo_1983_p6
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : c < a + b)
  (h₂ : b < a + c)
  (h₃ : a < b + c) :
  0 ≤ a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) := by
  have h₄ : a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) =
       a^3 * b - a^2 * b^2 + b^3 * c - b^2 * c^2 + c^3 * a - c^2 * a^2 := by
    ring_nf
  rw [h₄]
  have h₅ : 0 ≤ a^3 * b - a^2 * b^2 + b^3 * c - b^2 * c^2 + c^3 * a - c^2 * a^2 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a - c), sq_nonneg (b - a), sq_nonneg (c - b),
      mul_pos h₀.1 h₀.2.1, mul_pos h₀.2.1 h₀.2.2, mul_pos h₀.1 h₀.2.2,
      mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₂),
      mul_pos (sub_pos.mpr h₂) (sub_pos.mpr h₃),
      mul_pos (sub_pos.mpr h₃) (sub_pos.mpr h₁),
      sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b)]
  exact h₅
