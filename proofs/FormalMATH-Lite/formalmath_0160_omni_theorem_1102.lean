import Mathlib

theorem omni_theorem_1102 (p : ℝ) (hp : p ∈ Set.Icc 0 1)
    (h : (1 - p) * 0.7 + p * 0 = 0.5) :
    p = 2 / 7 := by
  field_simp [mul_comm, mul_assoc, mul_left_comm] at h
  ring_nf at h
  linarith
