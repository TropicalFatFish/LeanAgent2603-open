import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_495
  (a b : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : a % 10 = 2)
  (h₂ : b % 10 = 4)
  (h₃ : Nat.gcd a b = 6) :
  108 ≤ Nat.lcm a b := by
  by_contra h
  have hlcm_lt : Nat.lcm a b < 108 := Nat.lt_of_not_ge h
  have hlcm_pos : 0 < Nat.lcm a b := Nat.lcm_pos h₀.1 h₀.2
  have ha_le_lcm : a ≤ Nat.lcm a b :=
    Nat.le_of_dvd hlcm_pos (Nat.dvd_lcm_left a b)
  have hb_le_lcm : b ≤ Nat.lcm a b :=
    Nat.le_of_dvd hlcm_pos (Nat.dvd_lcm_right a b)
  have ha_lt : a < 108 := lt_of_le_of_lt ha_le_lcm hlcm_lt
  have hb_lt : b < 108 := lt_of_le_of_lt hb_le_lcm hlcm_lt
  have hga : 6 ∣ a := by
    simpa [h₃] using Nat.gcd_dvd_left a b
  have hgb : 6 ∣ b := by
    simpa [h₃] using Nat.gcd_dvd_right a b
  have ha_cases : a = 12 ∨ a = 42 ∨ a = 72 ∨ a = 102 := by
    rcases hga with ⟨u, hu⟩
    interval_cases a <;> omega
  have hb_cases : b = 24 ∨ b = 54 ∨ b = 84 := by
    rcases hgb with ⟨u, hu⟩
    interval_cases b <;> omega
  rcases ha_cases with rfl | rfl | rfl | rfl <;>
    rcases hb_cases with rfl | rfl | rfl
  all_goals
    norm_num [Nat.gcd, Nat.lcm] at h₃
  all_goals
    norm_num [Nat.gcd, Nat.lcm] at hlcm_lt
