import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_302 :
  (Complex.I / 2)^2 = -(1 / 4) := by
  norm_num [pow_two, Complex.I_sq]
  <;> ring_nf
  <;> simp [Complex.ext_iff]
  <;> norm_num
