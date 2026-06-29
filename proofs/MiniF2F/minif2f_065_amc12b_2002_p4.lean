import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem amc12b_2002_p4
  (n : ℕ)
  (h₀ : 0 < n)
  (h₁ : ((1 / 2 + 1 / 3 + 1 / 7 + 1 / n) : ℚ).den = 1) :
  n = 42 := by
  have hnz : (42 * n) ≠ 0 := by omega
  have hsum :
      ((1 / 2 + 1 / 3 + 1 / 7 + 1 / n) : ℚ) =
        ((41 * n + 42 : ℕ) : ℚ) / (42 * n : ℕ) := by
    field_simp [h₀.ne']
    norm_num
    ring
  rw [hsum] at h₁
  rw [Rat.den_div_natCast_eq_one_iff (41 * n + 42) (42 * n) hnz] at h₁
  rcases h₁ with ⟨c, hc⟩
  have hc0 : c ≠ 0 := by
    intro hc_zero
    rw [hc_zero, mul_zero] at hc
    omega
  have hc_le_one : c ≤ 1 := by
    by_contra h
    have hcge : 2 ≤ c := by omega
    have hmul : 42 * n * 2 ≤ 42 * n * c := Nat.mul_le_mul_left (42 * n) hcge
    nlinarith
  have hc_one : c = 1 := by omega
  rw [hc_one, mul_one] at hc
  omega
