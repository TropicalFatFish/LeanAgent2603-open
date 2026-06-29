import Mathlib

theorem aime_all_2007_I_2 (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4)
    (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c)
    (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    a = 52 := by
  have h1 : a = 6 * t := by linarith
  have h2 : b = 10 * (t - 2) := by
    nlinarith [hwalk, hbob]
  have h3 : c = 8 * (t - 4) := by linarith

  cases hmidway with
  | inl hmid1 =>
    have : a = (b + c) / 2 := hmid1
    rw [h1, h2, h3] at this
    linarith
  | inr hmid2 =>
    cases hmid2 with
    | inl hmid1 =>
      have : b = (a + c) / 2 := hmid1
      rw [h1, h2, h3] at this
      have hb_contra : t < 4 := by linarith
      linarith [hc]
    | inr hmid1 =>
      have : c = (a + b) / 2 := hmid1
      rw [h1, h2, h3] at this
      linarith
