import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1990_p4
  (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : x^2 - 10 * x - 29 ≠ 0)
  (h₂ : x^2 - 10 * x - 45 ≠ 0)
  (h₃ : x^2 - 10 * x - 69 ≠ 0)
  (h₄ : 1 / (x^2 - 10 * x - 29) + 1 / (x^2 - 10 * x - 45) - 2 / (x^2 - 10 * x - 69) = 0) :
  x = 13 := by
  set Q := x^2 - 10 * x

  have h_Q : Q = 39 := by
    have h₅ : 1 / (Q - 29) + 1 / (Q - 45) - 2 / (Q - 69) = 0 := by simpa [Q] using h₄
    have h₅₁ : Q - 29 ≠ 0 := by simpa [Q] using h₁
    have h₅₂ : Q - 45 ≠ 0 := by simpa [Q] using h₂
    have h₅₃ : Q - 69 ≠ 0 := by simpa [Q] using h₃
    field_simp at h₅
    ring_nf at h₅
    linarith

  have h_Q_eq_40 : Q = 39 := h_Q
  have h_QNQ : Q - 39 = 0 := by linarith

  have h_x_poly : x^2 - 10 * x - 39 = 0 := by linarith
  have h_factored : (x - 13) * (x + 3) = 0 := by
    ring_nf
    <;> simp_all
    <;> nlinarith

  have h_pos : x + 3 > 0 := by linarith
  have h_nonzero : x + 3 ≠ 0 := by linarith

  have h_sub : x - 13 = 0 := by
    apply mul_left_cancel₀ h_nonzero
    linarith

  linarith
