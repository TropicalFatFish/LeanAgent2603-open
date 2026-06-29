import Mathlib

theorem quantitative_reasoning_zh_blue_176 {l k : ℕ} (hl : l > 0) (hk : k > 0)
    (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4) :
    l = 3001 ∧ k = 2002 := by
  have h_k : k = 2002 := by
    have h1 : k * 180 = 360360 := by
      norm_num at h ⊢
      linarith
    have h2 : k = 2002 := by
      omega
    exact h2

  have h_l : l = 3001 := by
    rw [h_k] at h'
    omega

  exact ⟨h_l, h_k⟩
