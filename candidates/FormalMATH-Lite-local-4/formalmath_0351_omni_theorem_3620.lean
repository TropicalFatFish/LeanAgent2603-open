import Mathlib

theorem omni_theorem_3620 (f : ℝ → ℝ) :
    (∀ x y, f x + f (y * f x + f y) = f (x + 2 * f y) + x * y) ↔ ∀ x, f x = x + 1 := by
  apply Iff.intro
  · intro h
    have h0 : ∀ x, f x = x + 1 := by
      intro x
      have h1 := h 0 0
      have h2 := h 0 x
      have h3 := h x 0
      have h4 := h 1 1
      have h5 := h x 1
      have h6 := h 1 x
      simp at h1 h2 h3 h4 h5 h6 ⊢
      nlinarith [h0 0, h0 1, h2, h3, h5, h6]
    exact h0
  · intro h
    intro x y
    have h1 : f x = x + 1 := h x
    have h2 : f y = y + 1 := h y
    have h3 : ∀ z, f z = z + 1 := h
    simp [h1, h2, h3]
    <;> ring
    <;> linarith
