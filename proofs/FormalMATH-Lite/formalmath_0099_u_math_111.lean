import Mathlib

theorem u_math_111 (x : ℝ) :
  abs (-6 * x - 6) ≤ 1 ↔ x ∈ Set.Icc (-7 / 6) (-5 / 6) := by
  constructor
  · intro h
    rw [abs_le] at h
    constructor <;> nlinarith
  · intro h
    rw [Set.mem_Icc] at h
    rw [abs_le]
    constructor <;> nlinarith
