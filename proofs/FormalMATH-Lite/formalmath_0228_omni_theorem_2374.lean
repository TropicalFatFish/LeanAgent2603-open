import Mathlib

theorem omni_theorem_2374 {x : ℕ → ℤ} (h₀ : x 1 = 1) (h₁ : x 2 = 2)
    (h₂ : ∀ n, x (n + 1) = 2 * x n - x (n - 1) + 2 ^ n) :
    x 2012 = 2 ^ 2013 - 6036 := by
  have h_seq : ∀ n, x n = 2 ^ (n + 1) - 3 * n := by
    intro n
    induction n <;> simp_all [pow_succ, mul_add, add_mul, mul_one, zero_mul]
    <;> ring_nf at *
    <;> omega

  rw [h_seq]
  <;> norm_num
  <;> ring_nf
  <;> simp [pow_succ, mul_add, add_mul, mul_one, zero_mul, Int.sub_self]
  <;> rfl
