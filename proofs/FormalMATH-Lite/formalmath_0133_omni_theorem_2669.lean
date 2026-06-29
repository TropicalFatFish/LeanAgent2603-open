import Mathlib

theorem omni_theorem_2669 (x : ℤ) (hx : x = 2018) : x^2 + 2 * x - x * (x + 1) = 2018 := by
  have h : x^2 + 2 * x - x * (x + 1) = x := by
    ring_nf
  rw [h, hx]
  <;> rfl
