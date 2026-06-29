import Mathlib

open Real Set
open scoped Real

theorem quantitative_reasoning_zh_blue_655 (x : ℝ) :
    sin (π / 6) * sin (4 * π / 9) * sin x =
    sin (2 * π / 18) * sin (5 * π / 18) * sin (x + 4 * π / 18) ↔
    ∃ k : ℤ, x = k * π + π / 6 := by
  have h1 : sin (π / 6) = 1 / 2 := by
    rw [show sin (π / 6) = 1 / 2 by norm_num]
  have h2 : sin (4 * π / 9) = sin (8 * π / 18) := by ring
  have h3 : sin (2 * π / 18) = sin (π / 9) := by ring
  have h4 : sin (x + 4 * π / 18) = sin (x + 2 * π / 9) := by ring
  have h5 : (1 / 2 : ℝ) * sin (4 * π / 9) = sin (π / 9) * sin (5 * π / 18) := by
    rw [show sin (4 * π / 9) = sin (8 * π / 18) by ring]
    have := sin_two_mul (π / 9)
    have := sin_two_mul (2 * π / 9)
    field_simp
    ring_nf
    <;> norm_num
    <;> nlinarith [sin_sq_add_cos_sq (π / 9), sin_sq_add_cos_sq (2 * π / 9),
      sin_sq_add_cos_sq (5 * π / 18), sin_pos_pos_iff_pos_le (0) (π / 9),
      sin_pos_pos_iff_pos_le (0) (2 * π / 9), sin_pos_pos_iff_pos_le (0) (5 * π / 18)]
  rw [h1, h3, h4] at *
  rw [h5]
  constructor
  · intro h
    use 0
    have := sin_eq_sin_sub_int_mul_pi x (π / 6)
    apply this
    simpa using h
  · rintro ⟨k, hk⟩
    have := sin_eq_sin_sub_int_mul_pi_x
    rw [hk] at *
    have : sin (x + 4 * π / 18) = sin (x + 2 * π / 9) := by ring
    simp [this] at *
    rw [← sin_eq_sin_add_int_mul_pi x (π / 9)]
    simp
    <;> ring_nf
    <;> norm_num
