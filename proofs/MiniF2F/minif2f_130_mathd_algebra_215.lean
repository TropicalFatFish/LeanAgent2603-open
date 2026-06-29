import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_215
  (S : Finset ℝ)
  (h₀ : ∀ (x : ℝ), x ∈ S ↔ (x + 3)^2 = 121) :
  ∑ k ∈ S, k = -6 := by
  have h₁ : ∀ x : ℝ, (x + 3) ^ 2 = 121 ↔ x = 8 ∨ x = -14 := by
    intro x
    constructor
    · intro h
      have : x + 3 = 11 ∨ x + 3 = -11 := by
        apply eq_or_eq_neg_of_sq_eq_sq
        norm_num at h
        linarith
      cases this with
      | inl h' =>
        have : x = 8 := by linarith
        exact Or.inl this
      | inr h' =>
        have : x = -14 := by linarith
        exact Or.inr this
    · intro h
      cases h with
      | inl h =>
        rw [h]
        norm_num
      | inr h =>
        rw [h]
        norm_num
  have h₂ : ∀ x : ℝ, x ∈ S ↔ x = 8 ∨ x = -14 := by
    intro x
    rw [h₀]
    simpa [h₁] using h₁ x
  have h₃ : S = {8, -14} := by
    apply Finset.ext
    intro x
    simp only [h₂, Finset.mem_insert, Finset.mem_singleton]
  rw [h₃]
  norm_num
