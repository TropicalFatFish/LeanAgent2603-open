import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_amgm_sum1toneqn_prod1tonleq1
  (a : ℕ → NNReal)
  (n : ℕ)
  (h₀ : ∑ x ∈ Finset.range n, a x = n) :
  ∏ x ∈ Finset.range n, a x ≤ 1 := by
  by_cases hn : n = 0
  · rw [hn]
    simp
  · have h₁ : 0 < n := Nat.pos_of_ne_zero hn
    have h₂ : (∑ x ∈ Finset.range n, (a x : ℝ)) = (n : ℝ) := by
      norm_cast
      <;> simp [h₀]
    have h₃ : (∏ x ∈ Finset.range n, (a x : ℝ)) ≤ 1 := by
      have h₄ : (∏ x ∈ Finset.range n, (a x : ℝ)) ^ ((n : ℝ)⁻¹) ≤ (∑ x ∈ Finset.range n, (a x : ℝ)) / (n : ℝ) := by
        have h₄' : (∏ x ∈ Finset.range n, (a x : ℝ) ^ (1 : ℝ)) ^ ((∑ x ∈ Finset.range n, (1 : ℝ))⁻¹) ≤ (∑ x ∈ Finset.range n, (1 : ℝ) * (a x : ℝ)) / (∑ x ∈ Finset.range n, (1 : ℝ)) := by
          apply Real.geom_mean_le_arith_mean (Finset.range n) (fun _ => 1) (fun x => (a x : ℝ))
          · intro x hx
            norm_num
          · simp [Finset.sum_const, Finset.card_range]
            exact_mod_cast h₁
          · intro x hx
            exact NNReal.coe_nonneg (a x)
        have h₅' : (∑ x ∈ Finset.range n, (1 : ℝ)) = (n : ℝ) := by
          simp [Finset.sum_const, Finset.card_range]
        have h₆' : (∏ x ∈ Finset.range n, (a x : ℝ) ^ (1 : ℝ)) = (∏ x ∈ Finset.range n, (a x : ℝ)) := by
          simp [Finset.prod_const, pow_one]
        have h₇' : (∑ x ∈ Finset.range n, (1 : ℝ) * (a x : ℝ)) = (∑ x ∈ Finset.range n, (a x : ℝ)) := by
          simp [Finset.sum_const, mul_one]
        simp_all [h₅', h₆', h₇']
        <;> field_simp [h₁.ne']
        <;> ring
      have h₅ : (∑ x ∈ Finset.range n, (a x : ℝ)) / (n : ℝ) = 1 := by
        rw [h₂]
        field_simp [h₁.ne']
        <;> norm_cast
      rw [h₅] at h₄
      have h₆ : (∏ x ∈ Finset.range n, (a x : ℝ)) ≥ 0 := by positivity
      have h₇ : (∏ x ∈ Finset.range n, (a x : ℝ)) ^ ((n : ℝ)⁻¹) ≤ 1 := h₄
      have h₈ : (∏ x ∈ Finset.range n, (a x : ℝ)) ≤ 1 := by
        by_contra h
        have h₉ : (∏ x ∈ Finset.range n, (a x : ℝ)) > 1 := by linarith
        have h₁₀ : (∏ x ∈ Finset.range n, (a x : ℝ)) ^ ((n : ℝ)⁻¹) > 1 := by
          apply Real.one_lt_rpow
          · linarith
          · positivity
        linarith
      exact h₈
    norm_cast at h₃ ⊢
    <;> simp_all [NNReal.coe_le_coe]
