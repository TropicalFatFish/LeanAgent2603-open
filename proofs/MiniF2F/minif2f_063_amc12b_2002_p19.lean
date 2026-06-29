import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem amc12b_2002_p19
  (a b c: ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : a * (b + c) = 152)
  (h₂ : b * (c + a) = 162)
  (h₃ : c * (a + b) = 170) :
  a * b * c = 720 := by
  have h₁' : a * b + a * c = 152 := by linarith
  have h₂' : a * b + b * c = 162 := by linarith
  have h₃' : a * c + b * c = 170 := by linarith
  have h₄ : 2 * (a * b + b * c + a * c) = 484 := by linarith
  have h₅ : a * b + b * c + a * c = 242 := by linarith
  have h₆ : a * b = 72 := by
    linarith
  have h₇ : b * c = 90 := by
    linarith
  have h₈ : a * c = 80 := by
    linarith
  have h₉ : a * b * c = 720 := by
    have h₉' : a * b * c = (a * b) * c := by ring
    rw [h₉']
    have h₁₀ : a * b = 72 := h₆
    have h₁₁ : a * c = 80 := h₈
    have h₁₂ : c = 80 / a := by
      have h₁₃ : a * c = 80 := h₁₁
      field_simp [h₀.1.ne'] at h₁₃ ⊢
      linarith
    have h₁₃ : a * b = 72 := h₆
    subst h₁₂
    nlinarith [h₀.1.ne', h₀.2.1.ne', h₀.2.2.ne']
  exact h₉
