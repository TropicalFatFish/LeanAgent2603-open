import Mathlib

theorem omni_theorem_3332 (a b c d : ℕ) (ha : a = 5^56) (hb : b = 10^51) (hc : c = 17^35)
    (hd : d = 31^28) : a < d ∧ d < c ∧ c < b := by
  have h1 : 5^56 < 31^28 := by
    have : (5^56) < (31^28) := by norm_num
    exact this

  have h2 : 31^28 < 17^35 := by
    have : (31^28) < (17^35) := by norm_num
    exact this

  have h3 : 17^35 < 10^51 := by
    have : (17^35) < (10^51) := by norm_num
    exact this

  refine' ⟨_, _, _⟩
  · rw [ha, hd]; exact h1
  · rw [hd, hc]; exact h2
  · rw [hc, hb]; exact h3
