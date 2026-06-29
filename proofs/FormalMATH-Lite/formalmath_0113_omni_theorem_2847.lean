import Mathlib

open scoped Affine

theorem omni_theorem_2847 {A B C D : ℝ}
    (hA : A < B) (hB : B < C) (hC : C < D)
    (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1) :
    (B - A) / (D - C) = 1 / 2 := by
  have hA_pos : 0 < C - A := by linarith [hA, hB]
  have hB_pos : 0 < C - B := by linarith [hB, hA]
  have hC_pos : 0 < D - C := by linarith [hC, hB]
  field_simp [hA_pos] at hAB
  field_simp [hC_pos] at hBC
  have hAB_eq : C - A = 5 * (B - A) := by linarith
  have hCB_eq : C - B = (C - A) - (B - A) := by ring
  have hCB_eq2 : C - B = 4 * (B - A) := by linarith
  have hDC_eq : C - B = 2 * (D - C) := by linarith
  have hDC_eq2 : D - C = 2 * (B - A) := by linarith
  have h_final : (B - A) / (D - C) = 1 / 2 := by
    rw [hDC_eq2]
    have hA_ne_zero : B - A ≠ 0 := by linarith [hA]
    field_simp [hA_ne_zero]
    <;> ring
  exact h_final
