import Mathlib

theorem quantitative_reasoning_zh_blue_613 (f : ℝ → ℝ) (hf : Continuous f)
    (h : ∀ x y, 2 * f ((x + y) / 2) = f x + f y) :
    ∃ a b, ∀ x, f x = a * x + b ∧ a = f 1 - f 0 ∧ b = f 0 := by
  have hm : ∀ x y, f (midpoint ℝ x y) = midpoint ℝ (f x) (f y) := by
    intro x y
    have hh := h x y
    rw [midpoint_eq_smul_add, midpoint_eq_smul_add]
    norm_num [div_eq_mul_inv] at hh ⊢
    ring_nf at hh ⊢
    linarith
  let F : ℝ →ᵃ[ℝ] ℝ := AffineMap.ofMapMidpoint f hm hf
  refine ⟨F.linear 1, f 0, ?_⟩
  intro x
  have hmap0 := F.map_vadd (0 : ℝ) x
  change F (x + 0) = F.linear x + F 0 at hmap0
  simp at hmap0
  change f x = F.linear x + f 0 at hmap0
  have hlin : F.linear x = x * F.linear 1 := by
    simpa using (F.linear.map_smul x (1 : ℝ))
  have hone_map := F.map_vadd (0 : ℝ) (1 : ℝ)
  change F (1 + 0) = F.linear 1 + F 0 at hone_map
  simp at hone_map
  change f 1 = F.linear 1 + f 0 at hone_map
  constructor
  · rw [hmap0, hlin]
    ring
  · constructor
    · linarith
    · rfl
