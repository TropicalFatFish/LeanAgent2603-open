import Mathlib

open Finset Real

theorem aime_all_2015_I_1 {A B : ℤ}
    (hA : A = ∑ i ∈ range 19, ((2 * i + 1) * (2 * i + 2)) + 39)
    (hB : B = 1 + ∑ i ∈ range 19, ((2 * i + 2) * (2 * i + 3))) :
    |(A - B)| = 722 := by
  have h : A - B = -722 := by
    rw [hA, hB]
    simp [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_sub_distrib]
    ring_nf at *
    <;> norm_num
    <;> simp_all
    <;> norm_num
    <;> linarith
  rw [h]
  rw [abs_of_neg (show -722 < 0 by norm_num)]
  <;> norm_num
