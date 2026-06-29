import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1990_p15
  (a b x y : ℝ)
  (h₀ : a * x + b * y = 3)
  (h₁ : a * x^2 + b * y^2 = 7)
  (h₂ : a * x^3 + b * y^3 = 16)
  (h₃ : a * x^4 + b * y^4 = 42) :
  a * x^5 + b * y^5 = 20 := by

  have h₄ : (x + y) * (a * x ^ 2 + b * y ^ 2) - x * y * (a * x + b * y) = a * x ^ 3 + b * y ^ 3 := by
    ring

  rw [h₁, h₀] at h₄
  have h₅ : 7 * (x + y) - 3 * (x * y) = 16 := by
    linarith

  have h₆ : (x + y) * (a * x ^ 3 + b * y ^ 3) - x * y * (a * x ^ 2 + b * y ^ 2) = a * x ^ 4 + b * y ^ 4 := by
    ring

  rw [h₂, h₁] at h₆
  have h₇ : 16 * (x + y) - 7 * (x * y) = 42 := by
    linarith

  have h₈ : x + y = -14 := by
    nlinarith

  have h₉ : x * y = -38 := by
    nlinarith [h₅, h₈]

  have h₁₀ : a * x ^ 5 + b * y ^ 5 = (x + y) * (a * x ^ 4 + b * y ^ 4) - x * y * (a * x ^ 3 + b * y ^ 3) := by
    ring

  rw [h₁₀, h₈, h₉, h₃, h₂]
  norm_num
