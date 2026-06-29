import Mathlib

theorem omni_theorem_1485 {x y : ℝ} (h₀ : x - y = 4) (h₁ : x^3 - y^3 = 28) : x * y = -3 := by
  have h₂ : x^2 + x * y + y^2 = 7 := by
    have h₂a : x^3 - y^3 = (x - y) * (x^2 + x * y + y^2) := by ring
    rw [h₂a] at h₁
    rw [h₀] at h₁
    have h₂b : 4 * (x^2 + x * y + y^2) = 28 := by linarith
    linarith
  have h₃ : (x - y)^2 + 3 * (x * y) = x^2 + x * y + y^2 := by ring
  rw [h₀, h₂] at h₃
  linarith
