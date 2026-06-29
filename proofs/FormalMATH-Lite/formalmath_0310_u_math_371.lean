import Mathlib

def R (x y : ℕ) := 50 * x + 100 * y + 2 * x * y - 4 * x ^ 2 - 5 * y ^ 2
def P (x y : ℕ) := 38 * x + 76 * y + 2 * x * y - 160 - 4 * x ^ 2 - 5 * y ^ 2

theorem u_math_371 : R 8 10 = 804 ∧ P 8 10 = 308 := by
  unfold R P
  norm_num
