import Mathlib

open Real
open scoped BigOperators

theorem algebra_45698 (n : ℤ) (h : n ≡ 4 [ZMOD 9]) :
  ¬∃ x y z : ℤ, x^3 + y^3 + z^3 = n := by
  intro hxyz
  rcases hxyz with ⟨x, y, z, hxyz⟩
  have h1 := h
  have h2 := hxyz

  have h3 : (x^3) % 9 ∈ ({0, 1, 8} : Set ℤ) := by
    have hx : x % 9 = 0 ∨ x % 9 = 1 ∨ x % 9 = 2 ∨ x % 9 = 3 ∨ x % 9 = 4 ∨ x % 9 = 5 ∨ x % 9 = 6 ∨ x % 9 = 7 ∨ x % 9 = 8 := by
      omega
    rcases hx with (h | h | h | h | h | h | h | h | h) <;>
      simp [h, pow_succ, Int.mul_emod, Int.emod_emod] <;>
      norm_num <;>
      (try omega) <;>
      (try
        { contradiction })
  have h4 : (y^3) % 9 ∈ ({0, 1, 8} : Set ℤ) := by
    have hy : y % 9 = 0 ∨ y % 9 = 1 ∨ y % 9 = 2 ∨ y % 9 = 3 ∨ y % 9 = 4 ∨ y % 9 = 5 ∨ y % 9 = 6 ∨ y % 9 = 7 ∨ y % 9 = 8 := by
      omega
    rcases hy with (h | h | h | h | h | h | h | h | h) <;>
      simp [h, pow_succ, Int.mul_emod, Int.emod_emod] <;>
      norm_num <;>
      (try omega) <;>
      (try
        { contradiction })
  have h5 : (z^3) % 9 ∈ ({0, 1, 8} : Set ℤ) := by
    have hz : z % 9 = 0 ∨ z % 9 = 1 ∨ z % 9 = 2 ∨ z % 9 = 3 ∨ z % 9 = 4 ∨ z % 9 = 5 ∨ z % 9 = 6 ∨ z % 9 = 7 ∨ z % 9 = 8 := by
      omega
    rcases hz with (h | h | h | h | h | h | h | h | h) <;>
      simp [h, pow_succ, Int.mul_emod, Int.emod_emod] <;>
      norm_num <;>
      (try omega) <;>
      (try
        { contradiction })

  have h12 : (x^3 + y^3 + z^3) % 9 ≠ 4 := by
    rcases h3 with (r1 | r1 | r1) <;> rcases h4 with (r2 | r2 | r2) <;> rcases h5 with (r3 | r3 | r3) <;>
      (try
        {
          simp_all only [Int.ModEq, Int.add_emod]
          omega
        })
    <;> (try
      {
        simp_all only [Int.ModEq, Int.sub_emod, Int.add_emod]
        norm_num
        omega
      })
    <;> (try
      {
        simp_all [Int.ModEq, Int.add_emod]
        omega
      })
  have : (n) % 9 = 4 := by
    simp_all only [Int.ModEq, Int.emod_emod]
    omega
  omega
