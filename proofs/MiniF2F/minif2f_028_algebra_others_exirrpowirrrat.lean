import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_others_exirrpowirrrat :
  ∃ a b, Irrational a ∧ Irrational b ∧ ¬ Irrational (a^b) := by
  by_cases h : Irrational (Real.sqrt 2 ^ Real.sqrt 2)
  · use Real.sqrt 2 ^ Real.sqrt 2, Real.sqrt 2
    constructor
    · exact h
    constructor
    · exact irrational_sqrt_two
    · have h2 : (Real.sqrt 2 ^ Real.sqrt 2) ^ Real.sqrt 2 = 2 := by
        rw [← Real.rpow_mul (by positivity)]
        norm_num
        <;> field_simp [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        <;> ring_nf
        <;> norm_num
      rw [h2]
      intro hirr
      exact hirr ⟨2, by norm_num⟩
  · use Real.sqrt 2, Real.sqrt 2
    constructor
    · exact irrational_sqrt_two
    constructor
    · exact irrational_sqrt_two
    · exact h
