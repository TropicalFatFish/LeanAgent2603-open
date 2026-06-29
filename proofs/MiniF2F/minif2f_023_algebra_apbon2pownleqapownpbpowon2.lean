import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_apbon2pownleqapownpbpowon2
  (a b : ℝ)
  (n : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : 0 < n) :
  ((a + b) / 2)^n ≤ (a^n + b^n) / 2 := by
  have h₂ : ConvexOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ n) := by
    apply convexOn_pow
  have h₃ : a ∈ Set.Ici 0 := by
    exact Set.mem_Ici.mpr (by linarith [h₀.1])
  have h₄ : b ∈ Set.Ici 0 := by
    exact Set.mem_Ici.mpr (by linarith [h₀.2])
  have h₅ : (1 / 2 : ℝ) ≥ 0 := by norm_num
  have h₆ : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by norm_num
  have h₇ : (fun x : ℝ => x ^ n) ((1 / 2 : ℝ) * a + (1 / 2 : ℝ) * b) ≤ (1 / 2 : ℝ) * (fun x : ℝ => x ^ n) a + (1 / 2 : ℝ) * (fun x : ℝ => x ^ n) b := by
    apply h₂.2
    <;> simp_all [h₃, h₄, h₅, h₆]
    <;> linarith
  ring_nf at h₇ ⊢
  linarith
