import Mathlib

open Real

theorem omni_theorem_2677 {f : ℝ → ℝ → ℝ} (hf : ∀ a b, f a b = (a + b) / (a * b)) :
    f 3 6 = 1 / 2 := by
  rw [hf 3 6]
  field_simp
  norm_num
