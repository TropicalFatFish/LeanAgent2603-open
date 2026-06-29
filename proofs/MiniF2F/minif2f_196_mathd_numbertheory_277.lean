import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_277
  (m n : ℕ)
  (h₀ : Nat.gcd m n = 6)
  (h₁ : Nat.lcm m n = 126) :
  60 ≤ m + n := by
  have hm_le : m ≤ 126 := by
    have hm_dvd : m ∣ 126 := by
      simpa [h₁] using Nat.dvd_lcm_left m n
    exact Nat.le_of_dvd (by norm_num) hm_dvd
  have hn_le : n ≤ 126 := by
    have hn_dvd : n ∣ 126 := by
      simpa [h₁] using Nat.dvd_lcm_right m n
    exact Nat.le_of_dvd (by norm_num) hn_dvd
  have hm_dvd : m ∣ 126 := by
    simpa [h₁] using Nat.dvd_lcm_left m n
  have hn_dvd : n ∣ 126 := by
    simpa [h₁] using Nat.dvd_lcm_right m n
  have hgm : 6 ∣ m := by
    simpa [h₀] using Nat.gcd_dvd_left m n
  have hgn : 6 ∣ n := by
    simpa [h₀] using Nat.gcd_dvd_right m n
  have hprod : m * n = 756 := by
    rw [← Nat.gcd_mul_lcm m n, h₀, h₁]
  have hm_cases : m = 6 ∨ m = 18 ∨ m = 42 ∨ m = 126 := by
    rcases hm_dvd with ⟨u, hu⟩
    rcases hgm with ⟨v, hv⟩
    interval_cases m <;> omega
  have hn_cases : n = 6 ∨ n = 18 ∨ n = 42 ∨ n = 126 := by
    rcases hn_dvd with ⟨u, hu⟩
    rcases hgn with ⟨v, hv⟩
    interval_cases n <;> omega
  rcases hm_cases with rfl | rfl | rfl | rfl <;>
    rcases hn_cases with rfl | rfl | rfl | rfl
  all_goals omega
