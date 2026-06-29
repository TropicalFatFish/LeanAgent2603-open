import Mathlib

open Real

theorem aime_all_2001_I_2 (S : Finset ℝ) (hS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y)
    (hS1 : (S.sum id + 1) / (S.card + 1) = (S.sum id) / S.card - 13)
    (hS2 : (S.sum id + 2001) / (S.card + 1) = (S.sum id) / S.card + 27) :
    (S.sum id) / S.card = 651 := by
  have hn_nonzero : S.card ≠ 0 := by
    by_contra h
    have h' : S.card = 0 := by simpa [h]
    simp_all [h']
  field_simp [hn_nonzero] at hS1 hS2 ⊢
  ring_nf at hS1 hS2 ⊢
  linarith
