import Mathlib

def isNasty (f : Fin 5 → Fin 5) : Prop :=
  ¬∃ a b : Fin 5, a ≠ b ∧ f a = b ∧ f b = a

theorem omni_theorem_1953 :
    Set.ncard {f : Fin 5 → Fin 5 | isNasty f} = 1950 := by
  letI : DecidablePred (fun f : Fin 5 → Fin 5 => isNasty f) := by
    intro f
    unfold isNasty
    infer_instance
  rw [Set.ncard_eq_toFinset_card']
  simp only [Set.toFinset_setOf]
  native_decide
