import Mathlib

open Real Set
open scoped Real

lemma trig655_cos_diff :
    cos (π / 9) - cos (2 * π / 9) = sin (π / 18) := by
  rw [Real.cos_sub_cos]
  have h1 : ((π / 9 + 2 * π / 9) / 2) = π / 6 := by ring_nf
  have h2 : ((π / 9 - 2 * π / 9) / 2) = -π / 18 := by ring_nf
  rw [h1, h2]
  rw [Real.sin_pi_div_six]
  have hneg : sin (-π / 18) = -sin (π / 18) := by
    have hangle : -π / 18 = -(π / 18) := by ring_nf
    rw [hangle, Real.sin_neg]
  rw [hneg]
  ring

lemma trig655_const :
    sin (π / 6) * sin (4 * π / 9) =
      sin (2 * π / 18) * sin (5 * π / 18) *
        (cos (4 * π / 18) + 2 * sin (4 * π / 18) * cos (π / 6)) := by
  have hsin50 : sin (5 * π / 18) = cos (2 * π / 9) := by
    rw [← Real.sin_pi_div_two_sub (2 * π / 9)]
    congr 1
    ring_nf
  have hsin80 : sin (4 * π / 9) = 2 * sin (2 * π / 9) * cos (2 * π / 9) := by
    rw [show 4 * π / 9 = 2 * (2 * π / 9) by ring_nf]
    rw [Real.sin_two_mul]
  have hsin40 : sin (4 * π / 18) = sin (2 * π / 9) := by congr 1; ring_nf
  have hcos40 : cos (4 * π / 18) = cos (2 * π / 9) := by congr 1; ring_nf
  have hsin20 : sin (2 * π / 18) = sin (π / 9) := by congr 1; ring_nf
  have hsin40_double : sin (2 * π / 9) = 2 * sin (π / 9) * cos (π / 9) := by
    rw [show 2 * π / 9 = 2 * (π / 9) by ring_nf]
    rw [Real.sin_two_mul]
  have hbracket :
      cos (2 * π / 9) + 2 * sin (2 * π / 9) * cos (π / 6) = 2 * cos (π / 9) := by
    have hsum : 2 * sin (2 * π / 9) * cos (π / 6) =
        sin (7 * π / 18) + sin (π / 18) := by
      rw [Real.sin_add_sin]
      congr 1 <;> ring_nf
    have hsin70 : sin (7 * π / 18) = cos (π / 9) := by
      rw [← Real.sin_pi_div_two_sub (π / 9)]
      congr 1
      ring_nf
    have hsin10 : sin (π / 18) = cos (π / 9) - cos (2 * π / 9) :=
      trig655_cos_diff.symm
    rw [hsum, hsin70, hsin10]
    ring_nf
  rw [Real.sin_pi_div_six, hsin80, hsin50, hsin40, hcos40, hsin20, hbracket]
  rw [hsin40_double]
  ring_nf

lemma trig655_identity (x : ℝ) :
    sin (π / 6) * sin (4 * π / 9) * sin x -
      sin (2 * π / 18) * sin (5 * π / 18) * sin (x + 4 * π / 18) =
    (2 * sin (2 * π / 18) * sin (5 * π / 18) * sin (4 * π / 18)) *
      sin (x - π / 6) := by
  have hc := trig655_const
  rw [Real.sin_add, Real.sin_sub]
  rw [hc, Real.sin_pi_div_six]
  ring_nf

lemma trig655_C_pos :
    0 < 2 * sin (2 * π / 18) * sin (5 * π / 18) * sin (4 * π / 18) := by
  have h20 : 0 < sin (2 * π / 18) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · have hpi := Real.pi_pos
      nlinarith
  have h50 : 0 < sin (5 * π / 18) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · have hpi := Real.pi_pos
      nlinarith
  have h40 : 0 < sin (4 * π / 18) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · have hpi := Real.pi_pos
      nlinarith
  positivity

theorem quantitative_reasoning_zh_blue_655 (x : ℝ) :
    sin (π / 6) * sin (4 * π / 9) * sin x =
    sin (2 * π / 18) * sin (5 * π / 18) * sin (x + 4 * π / 18) ↔
    ∃ k : ℤ, x = k * π + π / 6 := by
  let C : ℝ := 2 * sin (2 * π / 18) * sin (5 * π / 18) * sin (4 * π / 18)
  have hCpos : 0 < C := by simpa [C] using trig655_C_pos
  have hCne : C ≠ 0 := ne_of_gt hCpos
  have hid := trig655_identity x
  constructor
  · intro h
    have hzero : C * sin (x - π / 6) = 0 := by
      dsimp [C]
      rw [← hid]
      rw [h]
      ring_nf
    have hsin : sin (x - π / 6) = 0 := by
      exact (mul_eq_zero.mp hzero).resolve_left hCne
    rcases Real.sin_eq_zero_iff.mp hsin with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    linarith
  · rintro ⟨k, hk⟩
    have hsin : sin (x - π / 6) = 0 := by
      apply Real.sin_eq_zero_iff.mpr
      refine ⟨k, ?_⟩
      linarith
    have hzero : C * sin (x - π / 6) = 0 := by simp [hsin]
    have hdiff : sin (π / 6) * sin (4 * π / 9) * sin x -
        sin (2 * π / 18) * sin (5 * π / 18) * sin (x + 4 * π / 18) = 0 := by
      rw [hid]
      simpa [C] using hzero
    linarith
