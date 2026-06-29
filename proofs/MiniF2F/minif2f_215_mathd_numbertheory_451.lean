import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_451
  (S : Finset ℕ)
  (h₀ : ∀ (n : ℕ), n ∈ S ↔ 2010 ≤ n ∧ n ≤ 2019 ∧ ∃ m, ((Nat.divisors m).card = 4 ∧ ∑ p ∈ (Nat.divisors m), p = n)) :
  ∑ k ∈ S, k = 2016 := by
  let good : Finset ℕ :=
    (Finset.Icc 2010 2019).filter
      (fun n =>
        ((Finset.range 2020).filter
          (fun m => (Nat.divisors m).card = 4 ∧
            ∑ p ∈ Nat.divisors m, p = n)).Nonempty)
  have hgood : good = {2016} := by
    native_decide
  have hS : S = good := by
    ext n
    rw [h₀ n]
    constructor
    · intro hn
      rcases hn with ⟨hnlo, hnhi, m, hcard, hsum⟩
      have hmpos : 0 < m := by
        by_contra hm
        have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
        simp [hm0] at hcard
      have hmmem : m ∈ Nat.divisors m := Nat.mem_divisors_self m (by omega)
      have hmle_sum : m ≤ ∑ p ∈ Nat.divisors m, p := by
        exact Finset.single_le_sum (fun p hp => Nat.zero_le p) hmmem
      have hmle : m ≤ 2019 := by
        rw [hsum] at hmle_sum
        omega
      have hmlt : m < 2020 := by omega
      refine Finset.mem_filter.mpr ?_
      refine ⟨Finset.mem_Icc.mpr ⟨hnlo, hnhi⟩, ?_⟩
      refine ⟨m, ?_⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hmlt, ⟨hcard, hsum⟩⟩
    · intro hmem
      rcases Finset.mem_filter.mp hmem with ⟨hnrange, hnonempty⟩
      rcases Finset.mem_Icc.mp hnrange with ⟨hnlo, hnhi⟩
      rcases hnonempty with ⟨m, hmfilter⟩
      rcases Finset.mem_filter.mp hmfilter with ⟨hmrange, hprop⟩
      rcases hprop with ⟨hcard, hsum⟩
      exact ⟨hnlo, hnhi, m, hcard, hsum⟩
  rw [hS, hgood]
  norm_num
