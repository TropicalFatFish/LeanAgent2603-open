import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem amc12a_2003_p5
  (A M C : ℕ)
  (h₀ : A ≤ 9 ∧ M ≤ 9 ∧ C ≤ 9)
  (h₁ : Nat.ofDigits 10 [0,1,C,M,A] + Nat.ofDigits 10 [2,1,C,M,A] = 123422) :
  A + M + C = 14 := by
  revert A M C h₀ h₁
  intro A M C h₀ h₁

  have hA : Nat.ofDigits 10 [0,1,C,M,A] = 10000*A + 1000*M + 100*C + 10*1 + 0 := by
    simp [Nat.ofDigits]
    <;> ring_nf
    <;> norm_num

  have hB : Nat.ofDigits 10 [2,1,C,M,A] = 10000*A + 1000*M + 100*C + 10*1 + 2 := by
    simp [Nat.ofDigits]
    <;> ring_nf
    <;> norm_num

  rw [hA, hB] at h₁
  ring_nf at h₁
  have h₂ : 200*A + 20*M + 2*C = 1234 := by
    omega
  have h₃ : 100*A + 10*M + C = 617 := by
    omega
  have h₄ : A = 6 := by
    omega
  have h₅ : M = 1 := by
    omega
  have h₆ : C = 7 := by
    omega
  subst_vars
  <;> norm_num
