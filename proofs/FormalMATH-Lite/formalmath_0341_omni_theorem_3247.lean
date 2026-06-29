import Mathlib

theorem omni_theorem_3247 (k : ℕ) (h : k % 7 = 3) :
    (3 * k) % 7 = 2 := by
  have h1 : k = 7 * (k / 7) + 3 := by
    have := Nat.mod_add_div k 7
    omega
  rw [h1]
  simp [mul_add, Nat.mul_mod, Nat.add_mod]
  <;> norm_num
