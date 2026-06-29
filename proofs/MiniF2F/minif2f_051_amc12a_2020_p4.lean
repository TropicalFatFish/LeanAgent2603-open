import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem amc12a_2020_p4
  (S : Finset ℕ)
  (h₀ : ∀ (n : ℕ), n ∈ S ↔ 1000 ≤ n ∧ n ≤ 9999 ∧ (∀ (d : ℕ), d ∈ Nat.digits 10 n → Even d) ∧ 5 ∣ n) :
  S.card = 100 := by
  have hS :
      S =
        (Finset.Icc 1000 9999).filter
          (fun n => (∀ (d : ℕ), d ∈ Nat.digits 10 n → Even d) ∧ 5 ∣ n) := by
    ext n
    rw [h₀ n]
    simp [and_assoc]
  rw [hS]
  native_decide
