import Mathlib

theorem algebra_68653 : ¬ ∃ x y : ℤ, x^3 + y^4 = 7 := by
  intro h
  rcases h with ⟨x, y, hxy⟩
  have this : (x^3 + y^4) % 13 = 7 % 13 := by
    simp [hxy]

  have h_n4 : ∀ n : ℤ, (n : ℤ)^4 % 13 = 0 ∨ (n : ℤ)^4 % 13 = 1 ∨ (n : ℤ)^4 % 13 = 3 ∨ (n : ℤ)^4 % 13 = 9 := by
    intro n
    have : (n : ℤ)^4 % 13 = ((n % 13 : ℤ)^4) % 13 := by
      simp [Int.pow_succ, Int.mul_emod]
    rw [this]
    have : (n % 13 : ℤ) = 0 ∨ (n % 13 : ℤ) = 1 ∨ (n % 13 : ℤ) = 2 ∨ (n % 13 : ℤ) = 3 ∨ (n % 13 : ℤ) = 4 ∨ (n % 13 : ℤ) = 5 ∨ (n % 13 : ℤ) = 6 ∨ (n % 13 : ℤ) = 7 ∨ (n % 13 : ℤ) = 8 ∨ (n % 13 : ℤ) = 9 ∨ (n % 13 : ℤ) = 10 ∨ (n % 13 : ℤ) = 11 ∨ (n % 13 : ℤ) = 12 := by
      omega
    rcases this with (h | h | h | h | h | h | h | h | h | h | h | h | h) <;>
      simp [h, pow_two, pow_succ, Int.mul_emod] <;> norm_num <;> omega

  have h_n3 : ∀ n : ℤ, (n : ℤ)^3 % 13 = 0 ∨ (n : ℤ)^3 % 13 = 1 ∨ (n : ℤ)^3 % 13 = 5 ∨ (n : ℤ)^3 % 13 = 8 ∨ (n : ℤ)^3 % 13 = 12 := by
    intro n
    have : (n : ℤ)^3 % 13 = ((n % 13 : ℤ)^3) % 13 := by
      simp [Int.pow_succ, Int.mul_emod]
    rw [this]
    have : (n % 13 : ℤ) = 0 ∨ (n % 13 : ℤ) = 1 ∨ (n % 13 : ℤ) = 2 ∨ (n % 13 : ℤ) = 3 ∨ (n % 13 : ℤ) = 4 ∨ (n % 13 : ℤ) = 5 ∨ (n % 13 : ℤ) = 6 ∨ (n % 13 : ℤ) = 7 ∨ (n % 13 : ℤ) = 8 ∨ (n % 13 : ℤ) = 9 ∨ (n % 13 : ℤ) = 10 ∨ (n % 13 : ℤ) = 11 ∨ (n % 13 : ℤ) = 12 := by
      omega
    rcases this with (h | h | h | h | h | h | h | h | h | h | h | h | h) <;>
      simp [h, pow_two, Int.mul_emod] <;> norm_num <;> omega

  rcases h_n4 y with (hy₁ | hy₁ | hy₁ | hy₁) <;>
    rcases h_n3 x with (hx₁ | hx₁ | hx₁ | hx₁ | hx₁) <;>
      omega
