import Mathlib

theorem omni_theorem_3492 (x : ℝ) (hx : x = 7.5 / 250) (h : y * x = 1.8) :
    y = 60 := by
  rw [hx] at h
  have h' : y * (7.5 / 250) = 1.8 := by exact h
  field_simp at h'
  norm_num at h' ⊢

  have : y = (9 / 5) / (7.5 / 250) := by
    field_simp [div_eq_mul_inv] at h' ⊢
    <;> ring_nf at h' ⊢
    <;> linarith
  rw [this]
  norm_num
