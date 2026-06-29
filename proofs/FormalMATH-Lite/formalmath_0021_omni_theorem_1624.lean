import Mathlib

open Finset Real

theorem omni_theorem_1624 {n : ℕ} (hn : 0 < n) (P : Fin n → ℝ)
    (hP : ∀ i, P i ∈ Set.Icc 0 1) :
    let m := n
    let E := ∑ i : Fin m, P i
    let Pr := 1 - ∏ i : Fin m, (1 - P i)
    E = ∑ i : Fin m, P i ∧ Pr = 1 - ∏ i : Fin m, (1 - P i) := by
  dsimp
  constructor <;> rfl
