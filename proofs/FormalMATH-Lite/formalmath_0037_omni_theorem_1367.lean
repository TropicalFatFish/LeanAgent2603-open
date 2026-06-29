import Mathlib

theorem omni_theorem_1367 {x : ℝ} (hx : x^3 + 4 * x = 8) : x^7 + 64 * x^2 = 128 := by
  have h1 : x^3 = 8 - 4 * x := by linarith
  calc
    x^7 + 64 * x^2 = x^3 * x^4 + 64 * x^2 := by ring
    _ = x^3 * (x * x^3) + 64 * x^2 := by ring
    _ = x * (x^3)^2 + 64 * x^2 := by ring
    _ = x * (8 - 4 * x)^2 + 64 * x^2 := by rw [h1]
    _ = 64 * x - 64 * x^2 + 16 * x^3 + 64 * x^2 := by ring
    _ = 64 * x + 16 * x^3 := by ring
    _ = 64 * x + 16 * (8 - 4 * x) := by rw [h1]
    _ = 64 * x + 128 - 64 * x := by ring
    _ = 128 := by ring
