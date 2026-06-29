import Mathlib

theorem omni_theorem_3157 (V : ℝ) (hV : V = 50) (v : ℝ) (hv : v = 2.5) :
    ⌊(V / v)⌋ = 20 := by
  rw [hV, hv]
  norm_num [Int.floor_eq_iff]
