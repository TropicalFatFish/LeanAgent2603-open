import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem numbertheory_4x3m7y3neq2003
  (x y : ℤ) :
  4 * x^3 - 7 * y^3 ≠ 2003 := by
  intro h

  have h₁ : (4 * x^3 - 7 * y^3) % 7 = 2003 % 7 := by
    have h' := congr_arg (fun k => k % 7) h
    simp at h' <;> omega

  norm_num at h₁

  simp [Int.mul_emod] at h₁

  have h₂ : x % 7 = 0 ∨ x % 7 = 1 ∨ x % 7 = 2 ∨ x % 7 = 3 ∨ x % 7 = 4 ∨ x % 7 = 5 ∨ x % 7 = 6 := by
    omega
  rcases h₂ with (h₂ | h₂ | h₂ | h₂ | h₂ | h₂ | h₂) <;>
  (try (
    simp [h₂, Int.pow_succ, Int.mul_emod] at h₁ ⊢ <;>
    omega
  ))
