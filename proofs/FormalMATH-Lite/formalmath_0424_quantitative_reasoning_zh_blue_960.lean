import Mathlib

theorem quantitative_reasoning_zh_blue_960 (a b : ℝ × ℝ)
    (h₀ : Real.sqrt (a.1^2 + a.2^2) = 5)
    (h₁ : Real.sqrt (b.1^2 + b.2^2) = 3)
    (h₂ : Real.sqrt ((a.1 - b.1)^2 + (a.2 - b.2)^2) = 6) :
    a.1 * b.1 + a.2 * b.2 = -1 := by
  have h₀' : a.1^2 + a.2^2 = 25 := by
    have h₀'' : 0 ≤ a.1^2 + a.2^2 := by positivity
    have h₀''' : (Real.sqrt (a.1^2 + a.2^2))^2 = a.1^2 + a.2^2 := Real.sq_sqrt h₀''
    calc
      a.1^2 + a.2^2 = (Real.sqrt (a.1^2 + a.2^2))^2 := by rw [h₀''']
      _ = 5^2 := by rw [h₀]
      _ = 25 := by norm_num

  have h₁' : b.1^2 + b.2^2 = 9 := by
    have h₁'' : 0 ≤ b.1^2 + b.2^2 := by positivity
    have h₁''' : (Real.sqrt (b.1^2 + b.2^2))^2 = b.1^2 + b.2^2 := Real.sq_sqrt h₁''
    calc
      b.1^2 + b.2^2 = (Real.sqrt (b.1^2 + b.2^2))^2 := by rw [h₁''']
      _ = 3^2 := by rw [h₁]
      _ = 9 := by norm_num

  have h₂' : (a.1 - b.1)^2 + (a.2 - b.2)^2 = 36 := by
    have h₂'' : 0 ≤ (a.1 - b.1)^2 + (a.2 - b.2)^2 := by positivity
    have h₂''' : (Real.sqrt ((a.1 - b.1)^2 + (a.2 - b.2)^2))^2 = (a.1 - b.1)^2 + (a.2 - b.2)^2 := Real.sq_sqrt h₂''
    calc
      (a.1 - b.1)^2 + (a.2 - b.2)^2 = (Real.sqrt ((a.1 - b.1)^2 + (a.2 - b.2)^2))^2 := by rw [h₂''']
      _ = 6^2 := by rw [h₂]
      _ = 36 := by norm_num

  have : (a.1 - b.1)^2 + (a.2 - b.2)^2 = (a.1^2 + a.2^2) + (b.1^2 + b.2^2) - 2 * (a.1 * b.1 + a.2 * b.2) := by
    ring

  rw [h₂'] at this
  rw [h₀', h₁'] at this

  norm_num at this
  linarith
