import Mathlib

theorem aime_all_2007_I_3 (b : ℝ) (hb : 0 < b) (z : ℂ) (hz : z = 9 + b * .I) (h : (z ^ 2).im = (z ^ 3).im) :
    b = 15 := by
  rw [hz] at h
  simp [Complex.ext_iff, pow_two, pow_three] at h
  simp [Complex.ext_iff, mul_comm, mul_assoc, sub_mul, add_mul, mul_sub, add_assoc, add_comm, add_left_comm] at h
  ring_nf at h ⊢
  have h1 : 18 * b = 243 * b - b ^ 3 := by linarith
  have h2 : 0 < b := hb
  have h3 : b * (225 - b ^ 2) = 0 := by linarith
  have h4 : 225 - b ^ 2 = 0 := by
    apply eq_of_sub_eq_zero
    apply mul_left_cancel₀ (show (b : ℝ) ≠ 0 by linarith)
    linarith
  rw [← sub_eq_zero] at h4
  have h5 : b ^ 2 = 225 := by linarith
  have h6 : b = 15 := by
    have h7 : b > 0 := hb
    nlinarith
  exact h6
