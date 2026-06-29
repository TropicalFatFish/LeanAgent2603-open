import Mathlib

theorem algebra_432962 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 1) :
    (x + y - 1)^2 / z + (y + z - 1)^2 / x + (z + x - 1)^2 / y ≥
    4 * (x + y + z) - 12 + 9 / (x + y + z) := by
  have hsum_pos : 0 < x + y + z := by linarith
  have h_main : ((x + y - 1)^2 / z + (y + z - 1)^2 / x + (z + x - 1)^2 / y) * (x + y + z) ≥ (2 * (x + y + z) - 3)^2 := by
    have h1 : 0 < z := hz
    have h2 : 0 < x := hx
    have h3 : 0 < y := hy
    have h4 : 0 < x * y := mul_pos h2 h3
    have h5 : 0 < z * x := mul_pos hz h2
    have h6 : 0 < y * z := mul_pos h3 hz
    field_simp
    nlinarith [sq_nonneg (x * (x + y - 1) - z * (y + z - 1)),
      sq_nonneg (y * (y + z - 1) - x * (z + x - 1)),
      sq_nonneg (z * (z + x - 1) - y * (x + y - 1))]
  calc
    (x + y - 1)^2 / z + (y + z - 1)^2 / x + (z + x - 1)^2 / y
    = ((x + y - 1)^2 / z + (y + z - 1)^2 / x + (z + x - 1)^2 / y) * (x + y + z) / (x + y + z) := by field_simp [hsum_pos]
    _ ≥ (2 * (x + y + z) - 3)^2 / (x + y + z) := by gcongr
    _ = (4 * (x + y + z) ^ 2 - 12 * (x + y + z) + 9) / (x + y + z) := by ring
    _ = 4 * (x + y + z) - 12 + 9 / (x + y + z) := by field_simp [hsum_pos]
    _ = 4 * (x + y + z) - 12 + 9 / (x + y + z) := by rfl
