import Mathlib

theorem algebra_413567 (x y : Fin 3 → ℝ)
    (h₀ : ∀ i, x i ^ 2 + y i ^ 2 = 1)
    (h₁ : ∑ i, x i = 0)
    (h₂ : ∑ i, y i = 0) :
    ∑ i, x i ^ 2 = 3 / 2 ∧ ∑ i, y i ^ 2 = 3 / 2 := by
  have h00 := h₀ 0
  have h01 := h₀ 1
  have h02 := h₀ 2
  simp [Fin.sum_univ_three] at h₁ h₂ ⊢
  have hx0 : x 0 * (x 0 + x 1 + x 2) = 0 := by rw [h₁]; ring
  have hx1 : x 1 * (x 0 + x 1 + x 2) = 0 := by rw [h₁]; ring
  have hx2 : x 2 * (x 0 + x 1 + x 2) = 0 := by rw [h₁]; ring
  have hy0 : y 0 * (y 0 + y 1 + y 2) = 0 := by rw [h₂]; ring
  have hy1 : y 1 * (y 0 + y 1 + y 2) = 0 := by rw [h₂]; ring
  have hy2 : y 2 * (y 0 + y 1 + y 2) = 0 := by rw [h₂]; ring
  ring_nf at hx0 hx1 hx2 hy0 hy1 hy2
  constructor <;> nlinarith [h00, h01, h02, hx0, hx1, hx2, hy0, hy1, hy2]
