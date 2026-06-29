import Mathlib

theorem omni_theorem_1345 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a^2 + a * b + b^2 = 9) (h2 : b^2 + b * c + c^2 = 52) (h3 : c^2 + c * a + a^2 = 49) :
    (49 * b^2 - 33 * b * c + 9 * c^2) / a^2 = 52 := by
  have h_main : 49 * b^2 - 33 * b * c + 9 * c^2 = 52 * a^2 := by
    nlinarith [h1, h2, h3, mul_pos ha hb, mul_pos hb hc, mul_pos hc ha]
  rw [h_main]
  field_simp [ha.ne']
  <;> ring_nf
