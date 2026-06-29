import Mathlib

theorem algebra_569850 {a : ℕ → ℤ} (ha1 : a 1 = 1000000)
    (han : ∀ n ≥ 1, a (n + 1) = n * ⌊(a n / n : ℝ)⌋ + n) :
    a 1 = 1000000 ∧ (∀ n ≥ 1, a (n + 1) = n * ⌊(a n / n : ℝ)⌋ + n) := by
  exact ⟨ha1, han⟩
