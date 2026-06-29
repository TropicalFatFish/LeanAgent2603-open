import Mathlib

def a : Fin 4 → ℤ := fun n => match n with
  | 0 => 222
  | 1 => 2222
  | 2 => 22222
  | 3 => 222222

theorem omni_theorem_2782 :
    {i | 3 ∣ a i}.encard = 2 := by
  simp [Set.encard]
  <;> decide
