import Mathlib

open scoped BigOperators

theorem omni_theorem_2844
  (b g : ℕ → ℕ)
  (hb0 : b 0 = 1)
  (hg0 : g 0 = 1)
  (hbn : ∀ n ≥ 1, b n = b (n - 1) + 2 * g (n - 1))
  (hgn : ∀ n ≥ 1, g n = g (n - 1) + g (n - 1))
  : (b 7 + g 7 = 383) := by
  have hg1 : g 1 = 2 := by
    have h := hgn 1 (by linarith)
    simp [hg0] at h ⊢
    linarith

  have hg2 : g 2 = 4 := by
    have h := hgn 2 (by linarith)
    simp [hg1] at h ⊢
    linarith

  have hg3 : g 3 = 8 := by
    have h := hgn 3 (by linarith)
    simp [hg2] at h ⊢
    linarith

  have hg4 : g 4 = 16 := by
    have h := hgn 4 (by linarith)
    simp [hg3] at h ⊢
    linarith

  have hg5 : g 5 = 32 := by
    have h := hgn 5 (by linarith)
    simp [hg4] at h ⊢
    linarith

  have hg6 : g 6 = 64 := by
    have h := hgn 6 (by linarith)
    simp [hg5] at h ⊢
    linarith

  have hg7 : g 7 = 128 := by
    have h := hgn 7 (by linarith)
    simp [hg6] at h ⊢
    linarith

  have hb1 : b 1 = 3 := by
    have h := hbn 1 (by linarith)
    simp [hg0] at h ⊢
    linarith

  have hb2 : b 2 = 7 := by
    have h := hbn 2 (by linarith)
    simp [hg1, hb1] at h ⊢
    linarith

  have hb3 : b 3 = 15 := by
    have h := hbn 3 (by linarith)
    simp [hg2, hb2] at h ⊢
    linarith

  have hb4 : b 4 = 31 := by
    have h := hbn 4 (by linarith)
    simp [hg3, hb3] at h ⊢
    linarith

  have hb5 : b 5 = 63 := by
    have h := hbn 5 (by linarith)
    simp [hg4, hb4] at h ⊢
    linarith

  have hb6 : b 6 = 127 := by
    have h := hbn 6 (by linarith)
    simp [hg5, hb5] at h ⊢
    linarith

  have hb7 : b 7 = 255 := by
    have h := hbn 7 (by linarith)
    simp [hg6, hb6] at h ⊢
    linarith

  calc
    b 7 + g 7 = 255 + 128 := by rw [hb7, hg7]
    _ = 383 := by norm_num
