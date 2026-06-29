import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem induction_pord1p1on2powklt5on2
  (n : ℕ)
  (h₀ : 0 < n) :
  ∏ k ∈ Finset.Icc 1 n, (1 + (1:ℝ) / 2^k) < 5 / 2 := by
  let f : ℕ → ℝ := fun k => 1 + (1 : ℝ) / 2 ^ k
  have hf_nonneg : ∀ k, 0 ≤ f k := by
    intro k
    dsimp [f]
    positivity
  have h_tail : ∀ n : ℕ, 3 ≤ n → ∏ k ∈ Finset.Icc 1 n, f k ≤ (5 : ℝ) / 2 * (1 - (1 : ℝ) / 2 ^ n) := by
    intro n hn
    induction n with
    | zero => omega
    | succ n ih =>
        by_cases hn3 : 3 ≤ n
        · have ih' := ih hn3
          rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ n + 1)]
          have hterm_nonneg : 0 ≤ f (n + 1) := hf_nonneg (n + 1)
          calc
            (∏ k ∈ Finset.Icc 1 n, f k) * f (n + 1)
                ≤ ((5 : ℝ) / 2 * (1 - (1 : ℝ) / 2 ^ n)) * f (n + 1) :=
                  mul_le_mul_of_nonneg_right ih' hterm_nonneg
            _ ≤ (5 : ℝ) / 2 * (1 - (1 : ℝ) / 2 ^ (n + 1)) := by
                  dsimp [f]
                  have hp : 0 < (2 : ℝ) ^ n := by positivity
                  rw [pow_succ]
                  field_simp [hp.ne']
                  ring_nf
                  nlinarith [hp]
        · have hn_eq : n = 2 := by omega
          subst n
          norm_num [f, Finset.prod_Icc_succ_top]
  by_cases hn3 : 3 ≤ n
  · have hbound := h_tail n hn3
    have hlt : (5 : ℝ) / 2 * (1 - (1 : ℝ) / 2 ^ n) < 5 / 2 := by
      have hp : 0 < (2 : ℝ) ^ n := by positivity
      nlinarith [one_div_pos.mpr hp]
    simpa [f] using lt_of_le_of_lt hbound hlt
  · have hn_small : n = 1 ∨ n = 2 := by omega
    rcases hn_small with rfl | rfl
    · norm_num [Finset.prod_Icc_succ_top]
    · norm_num [Finset.prod_Icc_succ_top]
