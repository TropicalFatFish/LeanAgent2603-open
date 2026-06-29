import Mathlib

theorem u_math_497 (x : ℝ) (hx : x ≠ -1 ∧ x ≠ -1 / 2) :
    (x - 1) / (x + 1) - (2 * x + 3) / (2 * x + 1) = (-6 * x - 4) / ((x + 1) * (2 * x + 1)) := by
  have h1 : (x + 1) ≠ 0 := by
    intro h
    have : x = -1 := by linarith
    have hx' : x ≠ -1 := hx.1
    exact hx' this
  have h2 : (2 * x + 1) ≠ 0 := by
    intro h
    have : x = -1 / 2 := by linarith
    have hx' : x ≠ -1 / 2 := hx.2
    exact hx' this
  field_simp [h1, h2]
  ring_nf at h1 h2 ⊢
  field_simp [h1, h2]
  ring_nf
  <;> linarith
