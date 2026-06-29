import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1988_p8
  (f : ℕ → ℕ → ℝ)
  (h₀ : ∀ x, 0 < x → f x x = x)
  (h₁ : ∀ x y, (0 < x ∧ 0 < y) → f x y = f y x)
  (h₂ : ∀ x y, (0 < x ∧ 0 < y) → (↑x + ↑y) * f x y = y * (f x (x + y))) :
  f 14 52 = 364 := by
  have e1 := h₂ 14 38 (by norm_num : 0 < 14 ∧ 0 < 38)
  have e2 := h₂ 14 24 (by norm_num : 0 < 14 ∧ 0 < 24)
  have e3 := h₂ 14 10 (by norm_num : 0 < 14 ∧ 0 < 10)
  have s1 := h₁ 14 10 (by norm_num : 0 < 14 ∧ 0 < 10)
  have e4 := h₂ 10 4 (by norm_num : 0 < 10 ∧ 0 < 4)
  have s2 := h₁ 10 4 (by norm_num : 0 < 10 ∧ 0 < 4)
  have e5 := h₂ 4 6 (by norm_num : 0 < 4 ∧ 0 < 6)
  have e6 := h₂ 4 2 (by norm_num : 0 < 4 ∧ 0 < 2)
  have s3 := h₁ 4 2 (by norm_num : 0 < 4 ∧ 0 < 2)
  have e7 := h₂ 2 2 (by norm_num : 0 < 2 ∧ 0 < 2)
  have b := h₀ 2 (by norm_num : 0 < 2)
  norm_num at e1 e2 e3 e4 e5 e6 e7 b
  nlinarith [e1, e2, e3, s1, e4, s2, e5, e6, s3, e7, b]
