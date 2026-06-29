import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3
  (a b c : ℝ)
  (h₀ : a ≤ b ∧ b ≤ c)
  (h₁ : a + b + c = 2)
  (h₂ : a * b + b * c + c * a = 1) :
  0 ≤ a ∧ a ≤ 1 / 3 ∧ 1 / 3 ≤ b ∧ b ≤ 1 ∧ 1 ≤ c ∧ c ≤ 4 / 3 := by
  have h_sum2 : a ^ 2 + b ^ 2 + c ^ 2 = 2 := by
    nlinarith [pow_two_nonneg (a + b + c)]

  have h₁_ : 0 ≤ a := by
    nlinarith [sq_nonneg (a - (a + b + c) / 3),
      sq_nonneg (b - (a + b + c) / 3),
      sq_nonneg (c - (a + b + c) / 3)]

  have h₂_ : a ≤ 1 / 3 := by
    nlinarith [sq_nonneg (a - 1 / 3),
      sq_nonneg (b - 1 / 3),
      sq_nonneg (c - 1 / 3)]

  have h₃_ : 1 / 3 ≤ b := by
    have := h₀.1
    have := h₀.2
    nlinarith [sq_nonneg (a - 1 / 3),
      sq_nonneg (b - 1 / 3),
      sq_nonneg (c - 1 / 3),
      h₁, h₂, h₁_]

  have h₄_ : b ≤ 1 := by
    have := h₀.1
    have := h₀.2
    nlinarith [sq_nonneg (a - 1),
      sq_nonneg (b - 1),
      sq_nonneg (c - 1),
      h₁, h₂, h₁_]

  have h₅_ : 1 ≤ c := by
    have := h₀.1
    have := h₀.2
    nlinarith [sq_nonneg (a - 1),
      sq_nonneg (b - 1),
      sq_nonneg (c - 1),
      h₁, h₂]

  have h₆_ : c ≤ 4 / 3 := by
    have := h₀.1
    have := h₀.2
    nlinarith [sq_nonneg (a - 4 / 3),
      sq_nonneg (b - 4 / 3),
      sq_nonneg (c - 4 / 3),
      h₁, h₂]

  exact ⟨h₁_, h₂_, h₃_, h₄_, h₅_, h₆_⟩
