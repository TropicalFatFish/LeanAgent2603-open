import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem imo_1981_p6
  (f : ℕ → ℕ → ℕ)
  (g : ℕ → ℕ)
  (h₀ : ∀ y, f 0 y = y + 1)
  (h₁ : ∀ x, f (x + 1) 0 = f x 1)
  (h₂ : ∀ x y, f (x + 1) (y + 1) = f x (f (x + 1) y))
  (h₃ : g 0 = 2)
  (h₄ : ∀ n, g (n + 1) = 2^(g n)) :
  f 4 1981 = g 1983 - 3 := by
  have hf1 : ∀ y, f 1 y = y + 2 := by
    intro y
    induction y with
    | zero =>
        calc
          f 1 0 = f 0 1 := by simpa using h₁ 0
          _ = 2 := by rw [h₀]
    | succ y ih =>
        calc
          f 1 (y + 1) = f 0 (f 1 y) := by simpa using h₂ 0 y
          _ = f 1 y + 1 := by rw [h₀]
          _ = y + 3 := by omega
  have hf2 : ∀ y, f 2 y = 2 * y + 3 := by
    intro y
    induction y with
    | zero =>
        calc
          f 2 0 = f 1 1 := by simpa using h₁ 1
          _ = 3 := by simpa using hf1 1
          _ = 2 * 0 + 3 := by norm_num
    | succ y ih =>
        calc
          f 2 (y + 1) = f 1 (f 2 y) := by simpa using h₂ 1 y
          _ = f 2 y + 2 := by rw [hf1]
          _ = 2 * (y + 1) + 3 := by omega
  have hf3 : ∀ y, f 3 y + 3 = 2 ^ (y + 3) := by
    intro y
    induction y with
    | zero =>
        calc
          f 3 0 + 3 = f 2 1 + 3 := by rw [h₁ 2]
          _ = 2 ^ (0 + 3) := by rw [hf2]; norm_num
    | succ y ih =>
        calc
          f 3 (y + 1) + 3 = f 2 (f 3 y) + 3 := by rw [h₂ 2 y]
          _ = 2 * (f 3 y) + 3 + 3 := by rw [hf2]
          _ = 2 * (f 3 y + 3) := by omega
          _ = 2 * 2 ^ (y + 3) := by rw [ih]
          _ = 2 ^ (y + 1 + 3) := by
            rw [show y + 1 + 3 = (y + 3) + 1 by omega]
            rw [pow_succ]
            ring
  have hg2 : g 2 = 16 := by
    calc
      g 2 = 2 ^ (g 1) := by simpa using h₄ 1
      _ = 2 ^ (2 ^ (g 0)) := by rw [h₄ 0]
      _ = 16 := by rw [h₃]; norm_num
  have hf4 : ∀ y, f 4 y + 3 = g (y + 2) := by
    intro y
    induction y with
    | zero =>
        calc
          f 4 0 + 3 = f 3 1 + 3 := by rw [h₁ 3]
          _ = 2 ^ (1 + 3) := by rw [hf3]
          _ = g (0 + 2) := by rw [hg2]; norm_num
    | succ y ih =>
        calc
          f 4 (y + 1) + 3 = f 3 (f 4 y) + 3 := by rw [h₂ 3 y]
          _ = 2 ^ (f 4 y + 3) := by rw [hf3]
          _ = 2 ^ (g (y + 2)) := by rw [ih]
          _ = g (y + 1 + 2) := by
            rw [show y + 1 + 2 = (y + 2) + 1 by omega]
            simpa using (h₄ (y + 2)).symm
  have hmain := hf4 1981
  norm_num at hmain ⊢
  omega
