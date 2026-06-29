import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1984_p1
  (u : ℕ → ℚ)
  (h₀ : ∀ n, u (n + 1) = u n + 1)
  (h₁ : ∑ k ∈ Finset.range 98, u k.succ = 137) :
  ∑ k ∈ Finset.range 49, u (2 * k.succ) = 93 := by
  have h_u : ∀ n, u n = u 0 + ↑n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [h₀, ih]
      ring_nf
      <;> simp
      <;> linarith

  have h_sum1 : ∑ k ∈ Finset.range 98, u k.succ = 98 * u 0 + 4851 := by
    calc
      _ = ∑ k ∈ Finset.range 98, (u 0 + ↑(k.succ)) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [h_u (k.succ)]
      _ = 98 * u 0 + ∑ k ∈ Finset.range 98, ↑(k.succ) := by
        simp [Finset.sum_add_distrib]
      _ = 98 * u 0 + 4851 := by
        norm_num

  have h_u0_val : u 0 = -2357 / 49 := by
    have h₂ : 98 * u 0 + 4851 = 137 := by linarith
    have h₃ : 98 * u 0 = -4714 := by linarith
    have h₄ : u 0 = -4714 / 98 := by
      linarith
    norm_num at h₄ ⊢
    linarith

  have h_sum2 : ∑ k ∈ Finset.range 49, u (2 * k.succ) = 49 * u 0 + 2450 := by
    calc
      _ = ∑ k ∈ Finset.range 49, (u 0 + ↑(2 * k.succ)) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [h_u (2 * k.succ)]
      _ = 49 * u 0 + ∑ k ∈ Finset.range 49, ↑(2 * k.succ) := by
        simp [Finset.sum_add_distrib]
      _ = 49 * u 0 + 2450 := by
        norm_num

  calc
    ∑ k ∈ Finset.range 49, u (2 * k.succ)
      = 49 * u 0 + 2450 := by rw [h_sum2]
    _ = 49 * (-2357 / 49 : ℚ) + 2450 := by rw [h_u0_val]
    _ = -2357 + 2450 := by ring
    _ = 93 := by norm_num
