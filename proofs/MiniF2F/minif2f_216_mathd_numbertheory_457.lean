import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_457
  (n : ℕ)
  (h₀ : 0 < n)
  (h₁ : 80325∣(n !)) :
  17 ≤ n := by
  have h₂ : (17 : ℕ) ∣ 80325 := by norm_num
  have h₃ : (17 : ℕ) ∣ (n !) := dvd_trans h₂ h₁
  have h₄ : (17 : ℕ).Prime := by decide
  have h₅ : (17 : ℕ) ∣ (n !) ↔ 17 ≤ n := Nat.Prime.dvd_factorial h₄
  exact h₅.mp h₃
