import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem amc12b_2002_p7
  (a b c : ℕ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : b = a + 1)
  (h₂ : c = b + 1)
  (h₃ : a * b * c = 8 * (a + b + c)) :
  a^2 + (b^2 + c^2) = 77 := by
  rcases h₀ with ⟨h_lt_a, h_lt_b, h_lt_c⟩
  have h_c_eq_a : c = a + 2 := by linarith
  rw [h₁, h_c_eq_a] at h₃
  ring_nf at h₃
  have h_a2_eq_24 : a * (a + 2) = 24 := by
    have : a + 1 ≠ 0 := by linarith
    apply mul_left_cancel₀ this
    linarith
  have h_a_eq_4 : a = 4 := by
    have h_a_pos : 0 < a := h_lt_a
    have : a ≤ 5 := by
      by_contra h
      have : a ≥ 6 := by linarith
      have : a * (a + 2) ≥ 6 * 8 := by
        nlinarith
      linarith
    interval_cases a <;> norm_num at h_a2_eq_24 <;> linarith
  rw [h_a_eq_4]
  rw [show b = 5 by linarith]
  rw [show c = 6 by linarith]
  norm_num
