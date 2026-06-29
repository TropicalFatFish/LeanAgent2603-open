import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem amc12a_2020_p7
  (a : ℕ → ℕ)
  (h₀ : (a 0)^3 = 1)
  (h₁ : (a 1)^3 = 8)
  (h₂ : (a 2)^3 = 27)
  (h₃ : (a 3)^3 = 64)
  (h₄ : (a 4)^3 = 125)
  (h₅ : (a 5)^3 = 216)
  (h₆ : (a 6)^3 = 343) :
  ∑ k ∈ Finset.range 7, (6 * (a k)^2) - ↑(2 * ∑ k ∈ Finset.range 6, (a k)^2) = 658 := by
  have h₀a : a 0 = 1 := by
    have : (a 0) ^ 3 = 1 := h₀
    nlinarith [pow_three (a 0)]

  have h₁a : a 1 = 2 := by
    have : (a 1) ^ 3 = 8 := h₁
    nlinarith [pow_three (a 1)]

  have h₂a : a 2 = 3 := by
    have : (a 2) ^ 3 = 27 := h₂
    nlinarith [pow_three (a 2)]

  have h₃a : a 3 = 4 := by
    have : (a 3) ^ 3 = 64 := h₃
    nlinarith [pow_three (a 3)]

  have h₄a : a 4 = 5 := by
    have : (a 4) ^ 3 = 125 := h₄
    nlinarith [pow_three (a 4)]

  have h₅a : a 5 = 6 := by
    have : (a 5) ^ 3 = 216 := h₅
    nlinarith [pow_three (a 5)]

  have h₆a : a 6 = 7 := by
    have : (a 6) ^ 3 = 343 := h₆
    nlinarith [pow_three (a 6)]

  simp [Finset.sum_range_succ, h₀a, h₁a, h₂a, h₃a, h₄a, h₅a, h₆a]
  <;> norm_num
  <;> omega
