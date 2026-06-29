import Mathlib

theorem omni_theorem_1278 {f : ℝ → ℝ} (hf : ∃ p q : Polynomial ℝ, f = fun x => p.eval x / q.eval x)
    (h : ∀ x ≠ 0, 3 * f (1 / x) + 2 * f x / x = x ^ 2) : f (-2) = 67 / 20 := by
  obtain ⟨p, q, h_eq⟩ := hf

  have h2 : 3 * f (1 / 2) + f 2 = 4 := by
    specialize h 2 (by norm_num)
    field_simp at *
    ring_nf at *
    linarith

  have h3 : 3 * f (-1 / 2) - f (-2) = 4 := by
    specialize h (-2) (by norm_num)
    field_simp at *
    ring_nf at *
    linarith

  have h4 : 3 * f (-2) - 4 * f (-1 / 2) = 1 / 4 := by
    specialize h (-1 / 2) (by norm_num)
    field_simp at *
    ring_nf at *
    linarith

  linarith [h3, h4]
