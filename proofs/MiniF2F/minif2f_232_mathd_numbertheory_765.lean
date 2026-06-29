import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_765
  (x : ℤ)
  (h₀ : x < 0)
  (h₁ : (24 * x) % 1199 = 15) :
  x ≤ -449 := by
  have h₂ : x % 1199 = 750 := by
    have : (24 * 750) % 1199 = 15 := by
      norm_num
    have : (24 * x) % 1199 = (24 * (x % 1199)) % 1199 := by
      simp [Int.mul_emod]
    rw [this] at h₁
    omega
  have h₃ : ∃ (k : ℤ), x = 1199 * k + 750 := by
    use (x - 750) / 1199
    omega
  rcases h₃ with ⟨k, hk⟩
  rw [hk] at h₀
  omega
