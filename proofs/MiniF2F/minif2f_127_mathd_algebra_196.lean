import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_196
  (S : Finset ℝ)
  (h₀ : ∀ (x : ℝ), x ∈ S ↔ abs (2 - x) = 3) :
  ∑ k ∈ S, k = 4 := by
  have h₁ : ∀ x : ℝ, abs (2 - x) = 3 ↔ x = -1 ∨ x = 5 := by
    intro x
    constructor
    · intro h
      cases' le_total x 2 with hx1 hx2
      · have h₂ : 2 - x ≥ 0 := by linarith
        rw [abs_of_nonneg h₂] at h
        have h₃ : 2 - x = 3 := by linarith
        have h₄ : x = -1 := by linarith
        rw [h₄]
        simp
      · have h₂ : 2 - x ≤ 0 := by linarith
        rw [abs_of_nonpos h₂] at h
        have h₃ : 2 - x = -3 := by linarith
        have h₄ : x = 5 := by linarith
        rw [h₄]
        simp
    · rintro (rfl | rfl) <;> norm_num

  have h₂ : S = insert (-1 : ℝ) (insert 5 ∅) := by
    apply Finset.ext
    intro x
    simp [h₀, h₁]
    <;> tauto

  rw [h₂]
  simp [Finset.sum_insert, Finset.sum_singleton]
  <;> norm_num
