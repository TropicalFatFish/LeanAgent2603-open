import Mathlib

theorem quantitative_reasoning_zh_blue_560 (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    2 ≤ a ∧ b + c ≤ -4 := by
  have hb : b = -1 - a := by
    have hb' : a + b = -1 := by linarith
    linarith

  have hc : c = 3 - 2 * a := by
    linarith

  have h_disc : 9 * a ^ 2 - 10 * a + 1 > 0 := by
    have h_disc' : b ^ 2 - 4 * a * c = 9 * a ^ 2 - 10 * a + 1 := by
      rw [hb, hc]
      ring
    linarith

  have h_a_ge_2 : 2 ≤ a := by
    by_contra h
    have h_a_eq_1 : a = 1 := by
      omega
    rw [h_a_eq_1] at h_disc
    norm_num at h_disc

  have h_bc : b + c ≤ -4 := by
    rw [hb, hc]
    linarith

  exact ⟨h_a_ge_2, h_bc⟩
