import Mathlib

theorem aime_all_2007_II_4 (a b m : ℝ) (ha : 0 < a) (hb : 0 < b)
(h1 : 100 * a = 300 ∧ 100 * b = 200)
(h2 : 60 * 2 * a = 240 ∧ 60 * 2 * b = 300)
(h3 : 50 * 3 * a = 150 ∧ 50 * 3 * b = m) :
m = 450 := by
  have h1a : a = 3 := by linarith
  have h1b : b = 2 := by linarith
  have hb_val : 50 * 3 * b = 300 := by rw [h1b]; norm_num
  have hm : m = 300 := by linarith
  rw [hm]
  norm_num <;> linarith
