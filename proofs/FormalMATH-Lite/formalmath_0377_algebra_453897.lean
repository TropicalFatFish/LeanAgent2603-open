import Mathlib

theorem algebra_453897 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c ≥ a * b * c) :
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) := by
  have h1 : 6 / a + 3 / b + 2 / c ≥ 2 := by
    have h2 : 0 < a * b * c := by positivity
    have h3 : 0 < 6 := by norm_num
    have h4 : 0 < 3 := by norm_num
    have h5 : 0 < 2 := by norm_num
    field_simp [ha.ne', hb.ne', hc.ne']
    rw [add_comm]
    nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos hc ha,
      mul_pos ha (mul_pos hb hc)]
  have h2 : 6 / b + 3 / c + 2 / a ≥ 2 := by
    have h3 : 0 < a * b * c := by positivity
    field_simp [ha.ne', hb.ne', hc.ne']
    nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos hc ha,
      mul_pos ha (mul_pos hb hc)]
  exact Or.inl ⟨h1, h2⟩
