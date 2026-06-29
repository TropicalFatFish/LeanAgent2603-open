import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem numbertheory_notEquiv2i2jasqbsqdiv8 :
  ¬ (∀ a b : ℤ, (∃ i j, a = 2*i ∧ b=2*j) ↔ (∃ k, a^2 + b^2 = 8*k)) := by
  push_neg
  use 2, 4
  apply Or.inl
  constructor
  · use 1, 2
    norm_num [mul_assoc]
  · intro k
    norm_num
    norm_num at *
    omega
