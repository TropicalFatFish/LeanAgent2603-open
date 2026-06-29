import Mathlib

open Real Set
open scoped Real

theorem omni_theorem_1599 (A B : ℝ) (h₁ : sin A + sin B = 1) (h₂ : cos A + cos B = 3 / 2) :
    cos (A - B) = 5 / 8 := by
  have h₃ : (sin A + sin B)^2 + (cos A + cos B)^2 = 1 + (3 / 2)^2 := by
    rw [h₁, h₂]
    norm_num

  have h₄ : sin A ^ 2 + sin B ^ 2 + cos A ^ 2 + cos B ^ 2 + 2 * (cos A * cos B + sin A * sin B) = 13 / 4 := by
    rw [pow_two, pow_two] at h₃
    simp [sq, add_assoc] at h₃
    ring_nf at h₃
    linarith

  have h₅ : sin A ^ 2 + cos A ^ 2 = 1 := by rw [sin_sq_add_cos_sq]
  have h₆ : sin B ^ 2 + cos B ^ 2 = 1 := by rw [sin_sq_add_cos_sq]
  have h₇ : 2 * (cos A * cos B + sin A * sin B) = 5 / 4 := by
    linarith [h₃, h₅, h₆]

  have h₈ : cos A * cos B + sin A * sin B = 5 / 8 := by
    linarith [h₅, h₆, h₇]

  rw [cos_sub]
  linarith [h₈]
