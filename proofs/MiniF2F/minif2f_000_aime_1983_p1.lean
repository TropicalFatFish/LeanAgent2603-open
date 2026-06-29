import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1983_p1 (x y z w : ℕ) (ht : 1 < x ∧ 1 < y ∧ 1 < z) (hw : 0 ≤ w)
    (h0 : Real.log w / Real.log x = 24) (h1 : Real.log w / Real.log y = 40)
    (h2 : Real.log w / Real.log (x * y * z) = 12) : Real.log w / Real.log z = 60 := by
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (lt_trans zero_lt_one ht.1)
  have hypos : (0 : ℝ) < y := by exact_mod_cast (lt_trans zero_lt_one ht.2.1)
  have hzpos : (0 : ℝ) < z := by exact_mod_cast (lt_trans zero_lt_one ht.2.2)
  have hxlog : Real.log (x : ℝ) ≠ 0 := by
    have hx1 : (1 : ℝ) < x := by exact_mod_cast ht.1
    exact (Real.log_pos hx1).ne'
  have hylog : Real.log (y : ℝ) ≠ 0 := by
    have hy1 : (1 : ℝ) < y := by exact_mod_cast ht.2.1
    exact (Real.log_pos hy1).ne'
  have hzlog : Real.log (z : ℝ) ≠ 0 := by
    have hz1 : (1 : ℝ) < z := by exact_mod_cast ht.2.2
    exact (Real.log_pos hz1).ne'
  have hxyzlog : Real.log ((x : ℝ) * (y : ℝ) * (z : ℝ)) = Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ) := by
    rw [Real.log_mul (mul_pos hxpos hypos).ne' hzpos.ne', Real.log_mul hxpos.ne' hypos.ne']
  have h0' : Real.log (w : ℝ) = 24 * Real.log (x : ℝ) := by
    field_simp [hxlog] at h0 ⊢
    linarith
  have h1' : Real.log (w : ℝ) = 40 * Real.log (y : ℝ) := by
    field_simp [hylog] at h1 ⊢
    linarith
  have h2' : Real.log (w : ℝ) = 12 * (Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ)) := by
    rw [hxyzlog] at h2
    have hden : Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ) ≠ 0 := by
      have hx1 : (1 : ℝ) < x := by exact_mod_cast ht.1
      have hy1 : (1 : ℝ) < y := by exact_mod_cast ht.2.1
      have hz1 : (1 : ℝ) < z := by exact_mod_cast ht.2.2
      have : 0 < Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ) := by nlinarith [Real.log_pos hx1, Real.log_pos hy1, Real.log_pos hz1]
      exact this.ne'
    field_simp [hden] at h2 ⊢
    linarith
  have hzrel : Real.log (w : ℝ) = 60 * Real.log (z : ℝ) := by
    nlinarith
  field_simp [hzlog]
  linarith
