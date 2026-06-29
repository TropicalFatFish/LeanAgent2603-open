import Mathlib

theorem omni_theorem_2688 (total_students : ℕ) (h₀ : total_students = 30)
    (students_skating : ℕ) (students_skiing : ℕ) (students_both : ℕ)
    (h₁ : students_skating = 20) (h₂ : students_skiing = 9) (h₃ : students_both = 5) :
    total_students - (students_skating + students_skiing - students_both) = 6 := by
  rw [h₀, h₁, h₂, h₃]
  <;> norm_num
