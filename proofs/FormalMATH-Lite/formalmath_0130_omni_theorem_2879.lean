import Mathlib

open Real

theorem omni_theorem_2879 (n : ℝ) : 8 + 6 = n + 8 ↔ n = 6 := by
  constructor
  · intro h
    linarith [add_left_comm n (6 + 8)]
  · intro h
    rw [h]
    norm_num
