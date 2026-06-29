import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem amc12_2000_p1
  (i m o : ℕ)
  (h₀ : i ≠ m ∧ m ≠ o ∧ o ≠ i)
  (h₁ : i*m*o = 2001) :
  i+m+o ≤ 671 := by
  have div_cases (x : ℕ) (hx : x ∣ 2001) :
      x = 1 ∨ x = 3 ∨ x = 23 ∨ x = 29 ∨ x = 69 ∨ x = 87 ∨ x = 667 ∨ x = 2001 := by
    have hxle : x ≤ 2001 := Nat.le_of_dvd (by norm_num) hx
    interval_cases x <;> norm_num at hx <;> norm_num
  have hi : i ∣ 2001 := by
    use m * o
    rw [← h₁]
    ring
  have hm : m ∣ 2001 := by
    use i * o
    rw [← h₁]
    ring
  have ho : o ∣ 2001 := by
    use i * m
    rw [← h₁]
    ring
  rcases div_cases i hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases div_cases m hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases div_cases o ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all
