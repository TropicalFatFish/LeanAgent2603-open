import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem amc12_2000_p12
  (a m c : ℕ)
  (h₀ : a + m + c = 12) :
  a*m*c + a*m + m*c + a*c ≤ 112 := by
  have h₁ : a ≤ 12 := by omega
  have h₂ : m ≤ 12 := by omega
  have h₃ : c ≤ 12 := by omega
  interval_cases a <;> interval_cases m <;> interval_cases c <;> omega
