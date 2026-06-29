import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem amc12a_2021_p8
  (d : ℕ → ℕ)
  (h₀ : d 0 = 0)
  (h₁ : d 1 = 0)
  (h₂ : d 2 = 1)
  (h₃ : ∀ n≥3, d n = d (n - 1) + d (n - 3)) :
  Even (d 2021) ∧ Odd (d 2022) ∧ Even (d 2023) := by
  let P : ℕ → Prop := fun k =>
    d (7 * k) % 2 = 0 ∧
    d (7 * k + 1) % 2 = 0 ∧
    d (7 * k + 2) % 2 = 1 ∧
    d (7 * k + 3) % 2 = 1 ∧
    d (7 * k + 4) % 2 = 1 ∧
    d (7 * k + 5) % 2 = 0 ∧
    d (7 * k + 6) % 2 = 1
  have hrec (n : ℕ) (hn : 3 ≤ n) :
      d n % 2 = (d (n - 1) + d (n - 3)) % 2 := by
    rw [h₃ n hn, Nat.add_mod]
  have hP : ∀ k, P k := by
    intro k
    induction k with
    | zero =>
        have hd3 : d 3 = 1 := by
          have h := h₃ 3 (by norm_num)
          simp [h₀, h₁, h₂] at h
          exact h
        have hd4 : d 4 = 1 := by
          have h := h₃ 4 (by norm_num)
          simp [h₀, h₁, h₂, hd3] at h
          exact h
        have hd5 : d 5 = 2 := by
          have h := h₃ 5 (by norm_num)
          simp [h₀, h₁, h₂, hd3, hd4] at h
          exact h
        have hd6 : d 6 = 3 := by
          have h := h₃ 6 (by norm_num)
          simp [h₀, h₁, h₂, hd3, hd4, hd5] at h
          exact h
        simp [P, h₀, h₁, h₂, hd3, hd4, hd5, hd6]
    | succ k ih =>
        rcases ih with ⟨hk0, hk1, hk2, hk3, hk4, hk5, hk6⟩
        have hs0 : d (7 * (k + 1)) % 2 = 0 := by
          have h := hrec (7 * (k + 1)) (by omega)
          rw [show 7 * (k + 1) - 1 = 7 * k + 6 by omega,
              show 7 * (k + 1) - 3 = 7 * k + 4 by omega] at h
          rw [h, Nat.add_mod, hk6, hk4]
        have hs1 : d (7 * (k + 1) + 1) % 2 = 0 := by
          have h := hrec (7 * (k + 1) + 1) (by omega)
          rw [show 7 * (k + 1) + 1 - 1 = 7 * (k + 1) by omega,
              show 7 * (k + 1) + 1 - 3 = 7 * k + 5 by omega] at h
          rw [h, Nat.add_mod, hs0, hk5]
        have hs2 : d (7 * (k + 1) + 2) % 2 = 1 := by
          have h := hrec (7 * (k + 1) + 2) (by omega)
          rw [show 7 * (k + 1) + 2 - 1 = 7 * (k + 1) + 1 by omega,
              show 7 * (k + 1) + 2 - 3 = 7 * k + 6 by omega] at h
          rw [h, Nat.add_mod, hs1, hk6]
        have hs3 : d (7 * (k + 1) + 3) % 2 = 1 := by
          have h := hrec (7 * (k + 1) + 3) (by omega)
          rw [show 7 * (k + 1) + 3 - 1 = 7 * (k + 1) + 2 by omega,
              show 7 * (k + 1) + 3 - 3 = 7 * (k + 1) by omega] at h
          rw [h, Nat.add_mod, hs2, hs0]
        have hs4 : d (7 * (k + 1) + 4) % 2 = 1 := by
          have h := hrec (7 * (k + 1) + 4) (by omega)
          rw [show 7 * (k + 1) + 4 - 1 = 7 * (k + 1) + 3 by omega,
              show 7 * (k + 1) + 4 - 3 = 7 * (k + 1) + 1 by omega] at h
          rw [h, Nat.add_mod, hs3, hs1]
        have hs5 : d (7 * (k + 1) + 5) % 2 = 0 := by
          have h := hrec (7 * (k + 1) + 5) (by omega)
          rw [show 7 * (k + 1) + 5 - 1 = 7 * (k + 1) + 4 by omega,
              show 7 * (k + 1) + 5 - 3 = 7 * (k + 1) + 2 by omega] at h
          rw [h, Nat.add_mod, hs4, hs2]
        have hs6 : d (7 * (k + 1) + 6) % 2 = 1 := by
          have h := hrec (7 * (k + 1) + 6) (by omega)
          rw [show 7 * (k + 1) + 6 - 1 = 7 * (k + 1) + 5 by omega,
              show 7 * (k + 1) + 6 - 3 = 7 * (k + 1) + 3 by omega] at h
          rw [h, Nat.add_mod, hs5, hs3]
        exact ⟨hs0, hs1, hs2, hs3, hs4, hs5, hs6⟩
  have h288 := hP 288
  rcases h288 with ⟨h0p, h1p, h2p, h3p, h4p, h5p, h6p⟩
  have h2021 : d 2021 % 2 = 0 := by
    simpa using h5p
  have h2022 : d 2022 % 2 = 1 := by
    simpa using h6p
  have h2023 : d 2023 % 2 = 0 := by
    have h289 := hP 289
    exact h289.1
  constructor
  · rw [← Nat.not_odd_iff_even, Nat.odd_iff]
    omega
  constructor
  · rw [Nat.odd_iff]
    exact h2022
  · rw [← Nat.not_odd_iff_even, Nat.odd_iff]
    omega
