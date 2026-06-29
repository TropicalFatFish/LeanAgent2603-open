import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_137
  (x : ℕ)
  (h₀ : ↑x + (4:ℝ) / (100:ℝ) * ↑x = 598) :
  x = 575 := by
  have h₁ : (x : ℝ) * (1 + (4:ℝ) / (100:ℝ)) = 598 := by
    ring_nf at h₀ ⊢
    linarith
  have h₂ : (x : ℝ) = (598:ℝ) / (1 + (4:ℝ) / (100:ℝ)) := by
    field_simp [add_pos] at h₁ ⊢
    linarith
  have h₃ : (x : ℝ) = (575:ℝ) := by
    rw [h₂]
    field_simp
    <;> norm_num
  exact_mod_cast h₃
