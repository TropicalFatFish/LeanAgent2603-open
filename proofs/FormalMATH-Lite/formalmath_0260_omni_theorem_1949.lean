import Mathlib

open Finset

def f (x : ℕ) := Nat.choose 127 x % 8

set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem omni_theorem_1949 : ∑ i ∈ Icc 1 63, i * f i = 8096 := by
  native_decide
