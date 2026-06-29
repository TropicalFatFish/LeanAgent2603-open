import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_314
  (r n : ℕ)
  (h₀ : r = 1342 % 13)
  (h₁ : 0 < n)
  (h₂ : 1342∣n)
  (h₃ : n % 13 < r) :
  6710 ≤ n := by
  have hr : r = 3 := by
    norm_num [h₀]
  rcases h₂ with ⟨k, rfl⟩
  have hkge : 5 ≤ k := by
    by_contra h
    have hkle : k ≤ 4 := by omega
    interval_cases k
    · norm_num at h₁
    · norm_num [hr] at h₃
    · norm_num [hr] at h₃
    · norm_num [hr] at h₃
    · norm_num [hr] at h₃
  calc
    6710 = 1342 * 5 := by norm_num
    _ ≤ 1342 * k := Nat.mul_le_mul_left 1342 hkge
