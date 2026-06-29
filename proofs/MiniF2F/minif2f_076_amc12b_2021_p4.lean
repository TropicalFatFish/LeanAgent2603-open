import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem amc12b_2021_p4
  (m a : ℕ)
  (h₀ : 0 < m ∧ 0 < a)
  (h₁ : ↑m / ↑a = (3:ℝ) / 4) :
  (84 * ↑m + 70 * ↑a) / (↑m + ↑a) = (76:ℝ) := by
  have h₂ : (a : ℝ) ≠ 0 := by
    exact_mod_cast (by linarith : a ≠ 0)
  have h₃ : ↑m = (3 : ℝ) * ↑a / 4 := by
    field_simp [h₂] at h₁ ⊢
    <;> linarith
  field_simp [h₂, add_pos h₀.1 h₀.2]
  <;> rw [h₃]
  <;> ring_nf
  <;> field_simp [h₂]
  <;> linarith
