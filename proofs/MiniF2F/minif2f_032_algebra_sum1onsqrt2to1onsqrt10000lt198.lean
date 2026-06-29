import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
  ∑ k ∈ (Finset.Icc (2 : ℕ) 10000), (1 / Real.sqrt k) < 198 := by
  have hterm : ∀ k ∈ Finset.Icc (2 : ℕ) 10000,
      (1 : ℝ) / Real.sqrt (k : ℝ) <
        2 * (Real.sqrt (k : ℝ) - Real.sqrt ((k - 1 : ℕ) : ℝ)) := by
    intro k hk
    rcases Finset.mem_Icc.mp hk with ⟨hk2, hk10000⟩
    have hkpos_nat : 0 < k := by omega
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos_nat
    have hk2r : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    have hkm1_cast : (((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1) := by
      have hcast_add : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
        exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ k))
      linarith
    have hnonneg_mul : 0 ≤ (k : ℝ) * ((k - 1 : ℕ) : ℝ) := by positivity
    have hrhs_nonneg : 0 ≤ (k : ℝ) - (1 / 2 : ℝ) := by linarith
    have hsq : (k : ℝ) * ((k - 1 : ℕ) : ℝ) < ((k : ℝ) - (1 / 2 : ℝ)) ^ 2 := by
      rw [hkm1_cast]
      nlinarith
    have hsqrt_lt : Real.sqrt ((k : ℝ) * ((k - 1 : ℕ) : ℝ)) < (k : ℝ) - (1 / 2 : ℝ) := by
      rw [Real.sqrt_lt hnonneg_mul hrhs_nonneg]
      exact hsq
    have hmain : (1 : ℝ) < 2 * ((k : ℝ) - Real.sqrt ((k : ℝ) * ((k - 1 : ℕ) : ℝ))) := by
      nlinarith
    have hsqrt_mul : Real.sqrt ((k : ℝ) * ((k - 1 : ℕ) : ℝ)) =
        Real.sqrt (k : ℝ) * Real.sqrt ((k - 1 : ℕ) : ℝ) := by
      rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (k : ℝ))]
    rw [hsqrt_mul] at hmain
    have hsqrt_pos : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos_of_pos hkpos
    have hcalc :
        (1 : ℝ) / Real.sqrt (k : ℝ) <
          2 * (Real.sqrt (k : ℝ) - Real.sqrt ((k - 1 : ℕ) : ℝ)) := by
      rw [div_lt_iff₀ hsqrt_pos]
      nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (k : ℝ))]
    exact hcalc
  have hsum_lt :
      (∑ k ∈ Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt (k : ℝ)) <
        ∑ k ∈ Finset.Icc (2 : ℕ) 10000,
          2 * (Real.sqrt (k : ℝ) - Real.sqrt ((k - 1 : ℕ) : ℝ)) := by
    refine Finset.sum_lt_sum (fun k hk => (hterm k hk).le) ?_
    refine ⟨2, ?_, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    · exact hterm 2 (Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  have htel_base : ∀ n : ℕ, 1 ≤ n →
      (∑ k ∈ Finset.Icc (2 : ℕ) n,
          (Real.sqrt (k : ℝ) - Real.sqrt ((k - 1 : ℕ) : ℝ))) =
        Real.sqrt (n : ℝ) - Real.sqrt (1 : ℝ) := by
    intro n hn
    induction n with
    | zero => omega
    | succ n ih =>
        by_cases hn1 : n = 0
        · subst n
          simp
        · have hn_pos : 1 ≤ n := by omega
          have hsucc : (2 : ℕ) ≤ n + 1 := by omega
          rw [Finset.sum_Icc_succ_top hsucc]
          rw [ih hn_pos]
          have hsub : ((n + 1 - 1 : ℕ) : ℝ) = (n : ℝ) := by norm_num
          rw [hsub]
          ring
  have htel :
      (∑ k ∈ Finset.Icc (2 : ℕ) 10000,
          2 * (Real.sqrt (k : ℝ) - Real.sqrt ((k - 1 : ℕ) : ℝ))) = (198 : ℝ) := by
    calc
      (∑ k ∈ Finset.Icc (2 : ℕ) 10000,
          2 * (Real.sqrt (k : ℝ) - Real.sqrt ((k - 1 : ℕ) : ℝ)))
          = 2 * (∑ k ∈ Finset.Icc (2 : ℕ) 10000,
              (Real.sqrt (k : ℝ) - Real.sqrt ((k - 1 : ℕ) : ℝ))) := by
            rw [Finset.mul_sum]
      _ = 2 * (Real.sqrt (10000 : ℝ) - Real.sqrt (1 : ℝ)) := by
            rw [htel_base 10000 (by norm_num)]
            norm_num
      _ = (198 : ℝ) := by norm_num [Real.sqrt_sq_eq_abs]
  rw [htel] at hsum_lt
  simpa using hsum_lt
