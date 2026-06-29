import Mathlib

open Nat

theorem omni_theorem_3054 {a b : ℕ} (ha : 1 ≤ a ∧ a ≤ 9) (hb : 0 ≤ b ∧ b ≤ 9)
    (h : (10 * b + a) - (10 * a + b) = 54) : |(a : ℤ) - b| = 6 := by
  have h1 : (10 * b + a) - (10 * a + b) = 9 * b - 9 * a := by
    ring_nf
    <;> omega

  have h2 : 9 * b - 9 * a = 54 := by linarith

  have h3 : b ≥ a + 6 := by
    omega

  have h4 : b ≤ a + 6 := by
    omega

  have h5 : b = a + 6 := by
    omega

  have h6 : (b : ℤ) = (a : ℤ) + 6 := by
    norm_cast
    <;> omega

  have h7 : (a : ℤ) - b = -6 := by
    omega

  rw [h7]
  norm_num
