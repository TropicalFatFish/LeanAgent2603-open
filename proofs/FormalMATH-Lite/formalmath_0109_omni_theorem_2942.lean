import Mathlib

def Ewan_sequence : ℕ → ℕ
| n => 3 + 11 * n

theorem omni_theorem_2942 : ∃ n, Ewan_sequence n = 113 := by
  use 10
  rfl
