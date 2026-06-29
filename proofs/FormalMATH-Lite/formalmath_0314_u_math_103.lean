import Mathlib

open Real

theorem u_math_103 : (cos (70 * π / 180) * cos (10 * π / 180) + cos (80 * π / 180) * cos (20 * π / 180)) / (cos (68 * π / 180) * cos (8 * π / 180) + cos (82 * π / 180) * cos (22 * π / 180)) = 1 := by

  have cos_prod : ∀ (x y : ℝ), cos x * cos y = (cos (x + y) + cos (x - y)) / 2 := by
    intro x y
    have ha := cos_add x y
    have hb := cos_sub x y
    have : cos x * cos y = (cos (x + y) + cos (x - y)) / 2 := by
      rw [ha, hb]
      ring
    exact this

  have h_num : cos (70 * π / 180) * cos (10 * π / 180) + cos (80 * π / 180) * cos (20 * π / 180) =
      (cos (80 * π / 180) + cos (60 * π / 180) + cos (100 * π / 180) + cos (60 * π / 180)) / 2 := by
    have h1 : cos (70 * π / 180) * cos (10 * π / 180) = (cos (80 * π / 180) + cos (60 * π / 180)) / 2 := by
      rw [cos_prod]
      ring_nf
    have h2 : cos (80 * π / 180) * cos (20 * π / 180) = (cos (100 * π / 180) + cos (60 * π / 180)) / 2 := by
      rw [cos_prod]
      ring_nf
    rw [h1, h2]
    ring

  have h_den : cos (68 * π / 180) * cos (8 * π / 180) + cos (82 * π / 180) * cos (22 * π / 180) =
      (cos (76 * π / 180) + cos (60 * π / 180) + cos (104 * π / 180) + cos (60 * π / 180)) / 2 := by
    have h3 : cos (68 * π / 180) * cos (8 * π / 180) = (cos (76 * π / 180) + cos (60 * π / 180)) / 2 := by
      rw [cos_prod]
      ring_nf
    have h4 : cos (82 * π / 180) * cos (22 * π / 180) = (cos (104 * π / 180) + cos (60 * π / 180)) / 2 := by
      rw [cos_prod]
      ring_nf
    rw [h3, h4]
    ring

  have h_simpl_num : (cos (80 * π / 180) + cos (60 * π / 180) + cos (100 * π / 180) + cos (60 * π / 180)) / 2 = 1 / 2 := by
    have h5 : cos (100 * π / 180) = -cos (80 * π / 180) := by
      rw [← cos_pi_sub]
      congr 1
      ring_nf
    have h6 : cos (60 * π / 180) = 1 / 2 := by
      rw [show (60 : ℝ) * π / 180 = π / 3 by ring]
      norm_num [cos_pi_div_three]
    simp_all [add_assoc, add_left_comm]
    <;> field_simp
    <;> ring_nf
    <;> linarith

  have h_simpl_den : (cos (76 * π / 180) + cos (60 * π / 180) + cos (104 * π / 180) + cos (60 * π / 180)) / 2 = 1 / 2 := by
    have h7 : cos (104 * π / 180) = -cos (76 * π / 180) := by
      rw [← cos_pi_sub]
      congr 1
      ring_nf
    have h8 : cos (60 * π / 180) = 1 / 2 := by
      rw [show (60 : ℝ) * π / 180 = π / 3 by ring]
      norm_num [cos_pi_div_three]
    simp_all [add_assoc, add_left_comm]
    <;> field_simp
    <;> ring_nf
    <;> linarith

  rw [h_num, h_den] at *
  rw [h_simpl_num, h_simpl_den]
  <;> ring
