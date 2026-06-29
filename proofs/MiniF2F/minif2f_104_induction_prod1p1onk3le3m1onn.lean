import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem induction_prod1p1onk3le3m1onn
  (n : ℕ)
  (h₀ : 0 < n) :
  ∏ k ∈ Finset.Icc 1 n, (1 + (1:ℝ) / k^3) ≤ (3:ℝ) - 1 / ↑n := by
  let f : ℕ → ℝ := fun k => 1 + (1 : ℝ) / k ^ 3
  have hmain : ∀ n : ℕ, 0 < n → ∏ k ∈ Finset.Icc 1 n, f k ≤ (3 : ℝ) - 1 / (n : ℝ) := by
    intro n hn
    induction n with
    | zero => cases hn
    | succ n ih =>
        by_cases hn0 : n = 0
        · subst n
          norm_num [f]
        · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
          have ih' := ih hn_pos
          rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ n + 1)]
          have hterm_nonneg : 0 ≤ f (n + 1) := by
            dsimp [f]
            positivity
          calc
            (∏ k ∈ Finset.Icc 1 n, f k) * f (n + 1)
                ≤ ((3 : ℝ) - 1 / (n : ℝ)) * f (n + 1) :=
                  mul_le_mul_of_nonneg_right ih' hterm_nonneg
            _ ≤ (3 : ℝ) - 1 / ((n + 1 : ℕ) : ℝ) := by
                  dsimp [f]
                  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn_pos
                  have hn1R : 0 < (n : ℝ) + 1 := by positivity
                  norm_num [Nat.cast_add, Nat.cast_one]
                  field_simp [hnR.ne', hn1R.ne']
                  ring_nf
                  nlinarith [sq_nonneg ((n : ℝ) - 1)]
  simpa [f] using hmain n h₀
