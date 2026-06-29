import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_289
  (k t m n : ℕ)
  (h₀ : Nat.Prime m ∧ Nat.Prime n)
  (h₁ : t < k)
  (h₂ : k^2 - m * k + n = 0)
  (h₃ : t^2 - m * t + n = 0) :
  m^n + n^m + k^t + t^k = 20 := by
  have h₄ : n ≥ 2 := Nat.Prime.two_le h₀.2
  have h₅ : n = 0 := by
    have : m * k = k ^ 2 + n := by omega
    have : m * t = t ^ 2 + n := by omega
    nlinarith [h₁]
  linarith [h₄, h₅]
