import Mathlib

open Polynomial

theorem omni_theorem_2338 {P Q : Polynomial ℝ}
    (hQ : Q = X ^ 2 + C 2 * X + C 3)
    (hP : ∀ x, P.eval (Q.eval x) = x ^ 6 + 6 * x ^ 5 + 18 * x ^ 4 + 32 * x ^ 3 + 35 * x ^ 2 + 22 * x + 8) :
    P.eval 2 = 2 := by
  have h : Q.eval (-1) = 2 := by
    rw [hQ]; norm_num
  have h' : P.eval (Q.eval (-1)) = (-1) ^ 6 + 6 * (-1) ^ 5 + 18 * (-1) ^ 4 + 32 * (-1) ^ 3 + 35 * (-1) ^ 2 + 22 * (-1) + 8 := by
    apply hP
  rw [h] at h'
  simp [h']
  norm_num
  <;> field_simp
  <;> ring_nf
  <;> norm_num
