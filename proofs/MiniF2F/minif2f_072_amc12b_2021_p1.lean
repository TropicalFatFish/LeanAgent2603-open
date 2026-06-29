import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem amc12b_2021_p1
  (S : Finset ℤ)
  (h₀ : ∀ (x : ℤ), x ∈ S ↔ ↑(abs x) < 3 * Real.pi):
  S.card = 19 := by
  have hS : S = Finset.Icc (-9 : ℤ) 9 := by
    ext x
    rw [h₀, Finset.mem_Icc]
    constructor
    · intro hx
      have hlt10r : ((abs x : ℤ) : ℝ) < 10 := by
        linarith [Real.pi_lt_d2]
      have hlt10z : (abs x : ℤ) < 10 := by exact_mod_cast hlt10r
      have hle9 : (abs x : ℤ) ≤ 9 := by omega
      exact (abs_le.mp hle9)
    · intro hx
      have hle9 : (abs x : ℤ) ≤ 9 := (abs_le.mpr hx)
      have hle9r : ((abs x : ℤ) : ℝ) ≤ 9 := by exact_mod_cast hle9
      have h9 : (9 : ℝ) < 3 * Real.pi := by linarith [Real.pi_gt_three]
      linarith
  rw [hS, Int.card_Icc]
  norm_num [Int.toNat]
