import Mathlib

theorem omni_theorem_3562 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x + y / z = 2) (h2 : y + z / x = 2) (h3 : z + x / y = 2) :
    x + y + z = 3 := by
  field_simp at h1 h2 h3
  ring_nf at h1 h2 h3 ⊢
  have h4 : x = 1 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      mul_pos hx hy, mul_pos hy hz, mul_pos hz hx]
  nlinarith
