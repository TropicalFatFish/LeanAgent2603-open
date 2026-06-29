import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_absapbon1pabsapbleqsumabsaon1pabsa
  (a b : ℝ) :
  abs (a + b) / (1 + abs (a + b)) ≤ abs a / (1 + abs a) + abs b / (1 + abs b) := by
  have h₁ : 0 ≤ abs a := abs_nonneg a
  have h₂ : 0 ≤ abs b := abs_nonneg b
  have h₃ : 0 ≤ abs (a + b) := abs_nonneg (a + b)
  have h_tri : abs (a + b) ≤ abs a + abs b := abs_add_le a b
  have h_mono :
    abs (a + b) / (1 + abs (a + b)) ≤ (abs a + abs b) / (1 + abs a + abs b) := by
    field_simp
    nlinarith [h_tri]
  have h_subadd :
    (abs a + abs b) / (1 + abs a + abs b) ≤ abs a / (1 + abs a) + abs b / (1 + abs b) := by
    field_simp
    ring_nf
    have : 0 ≤ abs a * abs b := mul_nonneg h₁ h₂
    nlinarith [h₁, h₂, this, mul_self_nonneg (abs a - abs b)]
  calc
    abs (a + b) / (1 + abs (a + b)) ≤ (abs a + abs b) / (1 + abs a + abs b) := h_mono
    _ ≤ abs a / (1 + abs a) + abs b / (1 + abs b) := h_subadd
