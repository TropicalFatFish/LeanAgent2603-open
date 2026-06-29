import Mathlib

open Real

theorem omni_theorem_2243 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (h : a > b)
    (A B C D : ℝ × ℝ) (hA : A = (a, a^2)) (hB : B = (b, b^2))
    (hC : C = (-b, b^2)) (hD : D = (-a, a^2)) (h1 : dist A D + dist B C = dist A B + dist C D)
    (h2 : dist A B = 3 / 4) : a = 27 / 40 := by
  subst A; subst B; subst C; subst D
  have hab_pos : 0 < a - b := by linarith
  have habs_pos : 0 < a^2 - b^2 := by nlinarith
  have habs : |a - b| = a - b := abs_of_pos hab_pos
  have hsquares : |a^2 - b^2| = a^2 - b^2 := abs_of_pos habs_pos
  have habs2 : |-b + a| = a - b := by rw [show -b + a = a - b by ring, abs_of_pos hab_pos]
  have hsquares2 : |b^2 - a^2| = a^2 - b^2 := by
    rw [show b^2 - a^2 = -(a^2-b^2) by ring, abs_neg, abs_of_pos habs_pos]
  simp [dist, Prod.dist_eq, Real.dist_eq, habs, hsquares, habs2, hsquares2] at h1 h2
  rw [abs_of_pos (by nlinarith : 0 < a + a), abs_of_pos (by nlinarith : 0 < b + b)] at h1
  have hs : a + b = 3 / 4 := by linarith
  have hd_le : a ^ 2 - b ^ 2 ≤ a - b := by
    have hfac : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
    rw [hfac, hs]
    nlinarith
  rw [max_eq_left hd_le] at h2
  have hd : a - b = 3 / 4 := by linarith
  have hb0 : b = 0 := by linarith
  linarith
