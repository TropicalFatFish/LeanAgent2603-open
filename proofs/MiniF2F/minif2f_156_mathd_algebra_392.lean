import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_392
  (n : ℕ)
  (h₀ : Even n)
  (h₁ : ((n:ℤ) - 2)^2 + (n:ℤ)^2 + ((n:ℤ) + 2)^2 = 12296) :
  ((n - 2) * n * (n + 2)) / 8 = 32736 := by

  have h₂ : (n : ℤ)^2 = 4096 := by
    have : ((n:ℤ) - 2)^2 + (n:ℤ)^2 + ((n:ℤ) + 2)^2 = 3 * (n : ℤ)^2 + 8 := by
      ring
    rw [this] at h₁
    have h₃ : 3 * (n : ℤ)^2 + 8 = 12296 := h₁
    linarith

  have h₄ : n = 64 := by
    have h₅ : n * n = 4096 := by
      norm_cast at h₂ ⊢
      linarith
    have : n = 64 := by
      nlinarith
    exact this

  rw [h₄]
  <;> norm_num
