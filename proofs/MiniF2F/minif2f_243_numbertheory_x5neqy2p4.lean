import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem numbertheory_x5neqy2p4
  (x y : ℤ) :
  x^5 ≠ y^2 + 4 := by
  have hfifth : ∀ z : ℤ, z^5 % 11 = 0 ∨ z^5 % 11 = 1 ∨ z^5 % 11 = 10 := by
    intro z
    have hz : z % 11 = 0 ∨ z % 11 = 1 ∨ z % 11 = 2 ∨ z % 11 = 3 ∨
        z % 11 = 4 ∨ z % 11 = 5 ∨ z % 11 = 6 ∨ z % 11 = 7 ∨
        z % 11 = 8 ∨ z % 11 = 9 ∨ z % 11 = 10 := by
      omega
    rcases hz with (hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz) <;>
      simp [hz, pow_succ, Int.mul_emod]
    <;> norm_num
    <;> omega

  have hsquare : ∀ w : ℤ, (w^2 + 4) % 11 = 2 ∨ (w^2 + 4) % 11 = 4 ∨
      (w^2 + 4) % 11 = 5 ∨ (w^2 + 4) % 11 = 7 ∨
      (w^2 + 4) % 11 = 8 ∨ (w^2 + 4) % 11 = 9 := by
    intro w
    have hw : w % 11 = 0 ∨ w % 11 = 1 ∨ w % 11 = 2 ∨ w % 11 = 3 ∨
        w % 11 = 4 ∨ w % 11 = 5 ∨ w % 11 = 6 ∨ w % 11 = 7 ∨
        w % 11 = 8 ∨ w % 11 = 9 ∨ w % 11 = 10 := by
      omega
    rcases hw with (hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw) <;>
      simp [hw, pow_two, Int.add_emod, Int.mul_emod]
    <;> norm_num
    <;> omega

  intro h
  have hmod : x^5 % 11 = (y^2 + 4) % 11 := by
    rw [h]
  have hx := hfifth x
  have hy := hsquare y
  rcases hx with (hx | hx | hx) <;>
    rcases hy with (hy | hy | hy | hy | hy | hy) <;>
    omega
