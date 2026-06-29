import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_320
  (n : ℕ)
  (h₀ : n < 101)
  (h₁ : 101 ∣ (123456 - n)) :
  n = 34 := by
  have h₂ : 123456 % 101 = 34 := by
    norm_num
  have h₃ : n % 101 = 34 := by
    have h₄ : (123456 - n) % 101 = 0 := by
      rw [Nat.dvd_iff_mod_eq_zero] at h₁
      exact_mod_cast h₁
    have h₅ : 123456 % 101 = n % 101 := by
      omega
    have h₆ : n % 101 = 34 := by
      omega
    exact h₆
  have h₄ : n = 34 := by
    have h₅ : n < 101 := h₀
    have h₆ : n % 101 = 34 := h₃
    omega
  exact h₄
