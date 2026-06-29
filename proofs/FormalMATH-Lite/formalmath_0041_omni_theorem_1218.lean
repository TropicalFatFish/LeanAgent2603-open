import Mathlib

theorem omni_theorem_1218 : ∑ k ∈ ({1, 2, 3, 4} : Set ℕ), Nat.choose 10 k * Nat.choose (10 - k) (5 - k) = 7560 := by
  norm_num [Set.insert]
  <;> rfl
