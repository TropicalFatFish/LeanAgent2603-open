import Mathlib

open Real Set
open scoped BigOperators

theorem omni_theorem_1753 {c1 c2 u1 u2 : ℝ}
  (hc1 : 0 < c1) (hc2 : 0 < c2)
  (hu1 : 0 < u1) (hu2 : 0 < u2) :
  let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2) := by
  dsimp
  constructor
  · rfl
  · constructor
    · rfl
    · constructor <;> rfl
