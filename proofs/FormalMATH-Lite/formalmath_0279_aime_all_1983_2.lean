import Mathlib

open Real Set

theorem aime_all_1983_2 (f : ℝ → ℝ) (p : ℝ) (hp : 0 < p ∧ p < 15)
  (hf : ∀ x, f x = abs (x - p) + abs (x - 15) + abs (x - p - 15)) :
    IsLeast {y | ∃ x, y = f x ∧ p ≤ x ∧ x ≤ 15} 15 := by
  constructor
  ·
    refine' ⟨15, _, by linarith, by linarith⟩
    rw [hf]
    have h1 : 15 - p ≥ 0 := by linarith
    have h2 : 15 - 15 = 0 := by norm_num
    have h3 : 15 - p - 15 = -p := by ring
    rw [abs_of_nonneg h1, abs_of_nonpos (by linarith), abs_of_neg (by linarith)]
    ring_nf
  ·
    intro y hy
    rcases hy with ⟨x, rfl, hx_p, hx_15⟩
    rw [hf]
    have h1 : x - p ≥ 0 := by linarith
    have h2 : x - 15 ≤ 0 := by linarith
    have h3 : x - p - 15 ≤ 0 := by linarith
    rw [abs_of_nonneg h1, abs_of_nonpos h2, abs_of_nonpos h3]
    ring_nf
    linarith
