import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_170
  (S : Finset ℤ)
  (h₀ : ∀ (n : ℤ), n ∈ S ↔ abs (n - 2) ≤ 5 + 6 / 10) :
  S.card = 11 := by
  have h₁ : S = Finset.Icc (-3 : ℤ) 7 := by
    ext n
    simp [Finset.mem_Icc, h₀] at *
    norm_num at *
    constructor
    · intro hn
      simp_all [abs_le]
      linarith
    · intro hn
      simp_all [abs_le]
      linarith
  rw [h₁]
  decide
