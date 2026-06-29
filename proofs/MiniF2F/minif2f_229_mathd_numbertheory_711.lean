import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_711
  (m n : ℕ)
  (h₀ : 0 < m ∧ 0 < n)
  (h₁ : Nat.gcd m n = 8)
  (h₂ : Nat.lcm m n = 112) :
  72 ≤ m + n := by
  have hm_le : m ≤ 112 := by
    have hm_dvd : m ∣ 112 := by
      simpa [h₂] using Nat.dvd_lcm_left m n
    exact Nat.le_of_dvd (by norm_num) hm_dvd
  have hn_le : n ≤ 112 := by
    have hn_dvd : n ∣ 112 := by
      simpa [h₂] using Nat.dvd_lcm_right m n
    exact Nat.le_of_dvd (by norm_num) hn_dvd
  have hm_dvd : m ∣ 112 := by
    simpa [h₂] using Nat.dvd_lcm_left m n
  have hn_dvd : n ∣ 112 := by
    simpa [h₂] using Nat.dvd_lcm_right m n
  have hgm : 8 ∣ m := by
    simpa [h₁] using Nat.gcd_dvd_left m n
  have hgn : 8 ∣ n := by
    simpa [h₁] using Nat.gcd_dvd_right m n
  have hprod : m * n = 896 := by
    rw [← Nat.gcd_mul_lcm m n, h₁, h₂]
  have hm_cases : m = 8 ∨ m = 16 ∨ m = 56 ∨ m = 112 := by
    rcases hm_dvd with ⟨u, hu⟩
    rcases hgm with ⟨v, hv⟩
    interval_cases m <;> omega
  have hn_cases : n = 8 ∨ n = 16 ∨ n = 56 ∨ n = 112 := by
    rcases hn_dvd with ⟨u, hu⟩
    rcases hgn with ⟨v, hv⟩
    interval_cases n <;> omega
  rcases hm_cases with rfl | rfl | rfl | rfl <;>
    rcases hn_cases with rfl | rfl | rfl | rfl
  all_goals
    norm_num at hprod
  all_goals omega
