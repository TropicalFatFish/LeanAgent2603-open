import Mathlib

theorem omni_theorem_2697 {l w : ℝ} (hl : l = 3 / 5) (hw : l * w = 1 / 3) :
    w = 5 / 9 := by
  rw [hl] at hw
  field_simp at hw
  rw [mul_comm] at hw
  field_simp [mul_comm] at hw ⊢
  ring_nf at hw ⊢
  exact hw
