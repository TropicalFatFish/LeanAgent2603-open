import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_521
  (m n : ℕ)
  (h₀ : Even m)
  (h₁ : Even n)
  (h₂ : m - n = 2)
  (h₃ : m * n = 288) :
  m = 18 := by
  have h₄ : m = n + 2 := by
    omega
  rw [h₄] at h₃
  have h₅ : n * n + 2 * n = 288 := by
    simp [Nat.mul_add, Nat.add_mul] at h₃
    exact h₃
  have h₆ : n = 16 := by
    have h₇ : n * n + 2 * n = 288 := h₅
    nlinarith
  subst h₆
  omega
