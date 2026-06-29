import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_12 :
  Finset.card (Finset.filter (λ x => 20∣x) (Finset.Icc 15 85)) = 4 := by
  have h : Finset.filter (λ x => 20 ∣ x) (Finset.Icc 15 85) = {20, 40, 60, 80} := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hx
      rcases hx with ⟨h1, h2, h3⟩
      have : x = 20 ∨ x = 40 ∨ x = 60 ∨ x = 80 := by
        omega
      rcases this with (rfl | rfl | rfl | rfl)
      · norm_num
      · norm_num
      · norm_num
      · norm_num
    · rintro (rfl | rfl | rfl | rfl)
      · norm_num
      · norm_num
      · norm_num
      · norm_num
  rw [h]
  norm_num
