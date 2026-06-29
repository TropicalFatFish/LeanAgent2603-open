import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_452
  (a : ℕ → ℝ)
  (h₀ : ∀ n, a (n + 2) - a (n + 1) = a (n + 1) - a n)
  (h₁ : a 1 = 2 / 3)
  (h₂ : a 9 = 4 / 5) :
  a 5 = 11 / 15 := by

  have h_diff1 : a 5 - a 1 = 4 * (a 1 - a 0) := by

    have h1 : a 2 - a 1 = a 1 - a 0 := by linarith [h₀ 0]
    have h2 : a 3 - a 2 = a 1 - a 0 := by linarith [h₀ 1, h1]
    have h3 : a 4 - a 3 = a 1 - a 0 := by linarith [h₀ 2, h1, h2]
    have h4 : a 5 - a 4 = a 1 - a 0 := by linarith [h₀ 3, h1, h2, h3]
    have h5 : a 5 - a 1 = (a 5 - a 4) + (a 4 - a 3) + (a 3 - a 2) + (a 2 - a 1) := by ring
    rw [h5, h4, h3, h2, h1]
    ring

  have h_diff2 : a 9 - a 5 = 4 * (a 1 - a 0) := by

    have h1 : a 2 - a 1 = a 1 - a 0 := by linarith [h₀ 0]
    have h2 : a 3 - a 2 = a 1 - a 0 := by linarith [h₀ 1, h1]
    have h3 : a 4 - a 3 = a 1 - a 0 := by linarith [h₀ 2, h1, h2]
    have h4 : a 5 - a 4 = a 1 - a 0 := by linarith [h₀ 3, h1, h2, h3]
    have h5 : a 6 - a 5 = a 1 - a 0 := by linarith [h₀ 4, h1, h2, h3, h4]
    have h6 : a 7 - a 6 = a 1 - a 0 := by linarith [h₀ 5, h1, h2, h3, h4, h5]
    have h7 : a 8 - a 7 = a 1 - a 0 := by linarith [h₀ 6, h1, h2, h3, h4, h5, h6]
    have h8 : a 9 - a 8 = a 1 - a 0 := by linarith [h₀ 7, h1, h2, h3, h4, h5, h6, h7]
    have h9 : a 9 - a 5 = (a 9 - a 8) + (a 8 - a 7) + (a 7 - a 6) + (a 6 - a 5) := by ring
    rw [h9, h8, h7, h6, h5]
    ring

  have h_mid : 2 * a 5 = a 1 + a 9 := by
    linarith [h_diff1, h_diff2]

  have h_target : a 5 = (a 1 + a 9) / 2 := by
    linarith

  rw [h_target]
  rw [h₁, h₂]
  norm_num
