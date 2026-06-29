import Mathlib

open Real

theorem omni_theorem_1693 :
  IsLeast {x : ℝ | ∃ n : ℕ, x = 7.49 * n ∧ 12 * n ≥ 550} 344.54 := by
  constructor
  ·
    use 46
    constructor
    ·
      norm_num
    ·
      norm_num
  ·
    intro x hx
    rcases hx with ⟨n, rfl, hn⟩

    have h_n : n ≥ 46 := by
      have h := hn
      norm_num at h
      omega

    have h_mul : (7.49 : ℝ) * ↑n ≥ (7.49 : ℝ) * 46 := by
      have h_7_49_nonneg : 0 ≤ (7.49 : ℝ) := by norm_num
      have h_nat_ge : (46 : ℝ) ≤ (↑n : ℝ) := by exact_mod_cast h_n
      apply mul_le_mul_of_nonneg_left h_nat_ge h_7_49_nonneg

    norm_num at h_mul ⊢
    linarith
