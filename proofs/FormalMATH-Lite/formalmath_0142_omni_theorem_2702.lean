import Mathlib

open List

def sol := ((Ico 1000 10000).filter (fun n => Even (n % 10) ∧ Even ((n / 10) % 10) ∧ Even ((n / 100) % 10) ∧ Even ((n / 1000) % 10))).length

set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem omni_theorem_2702 : sol = 500 := by
  native_decide
