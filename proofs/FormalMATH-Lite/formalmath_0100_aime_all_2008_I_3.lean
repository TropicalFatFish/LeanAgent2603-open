import Mathlib

open scoped BigOperators

theorem aime_all_2008_I_3
  (d b j s : ℤ)
  (h₀ : d > 0)
  (h₁ : b > 0)
  (h₂ : j > 0)
  (h₃ : s > 0)
  (h₄ : 2*b+3*j+4*s=74)
  (h₅ : 2*j+3*s+4*b=91) :
  b^2+j^2+s^2=314 := by
  have h₆ : 4*j + 5*s = 57 := by linarith
  have h₇ : s = 5 := by
    omega
  have h₈ : j = 8 := by
    rw [h₇] at h₆
    omega
  have h₉ : b = 15 := by
    rw [h₈] at h₆
    omega
  rw [h₉, h₈, h₇]
  <;> norm_num
