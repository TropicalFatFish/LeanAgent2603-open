import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_541
  (m n : ℕ)
  (h₀ : 1 < m)
  (h₁ : 1 < n)
  (h₂ : m * n = 2005) :
  m + n = 406 := by

  have h₃ : m = 5 ∨ m = 401 ∨ m = 2005 := by
    have h₄ : m ∣ 2005 := by
      use n
      <;> simp [h₂]
    have : m ∣ 5 * 401 := by
      simpa [show 2005 = 5 * 401 by norm_num] using h₄

    have h₅ : m ≤ 2005 := Nat.le_of_dvd (by norm_num) h₄
    interval_cases m <;> norm_num at * <;>
    (try omega) <;>
    (try
      { cases' this with t t
        · ring_nf at t
          norm_num at t
          omega
        · ring_nf at t
          norm_num at t
          omega
        · norm_num
          omega })

  rcases h₃ with (h₃ | h₃ | h₃)
  ·
    rw [h₃] at h₂
    norm_num at h₂
    linarith
  ·
    rw [h₃] at h₂
    norm_num at h₂
    linarith
  ·
    rw [h₃] at h₂
    norm_num at h₂
    linarith
