import Mathlib

theorem quantitative_reasoning_zh_blue_599 {f g : ℝ → ℝ}
    (hf : ∀ x, f (-x) = f x) (hg : ∀ x, g (-x) = -g x)
    (hfg : ∀ x, f x + g x = 1993 * x * Real.sqrt (9 - x ^ 2) + x ^ 1994) :
    ∀ x, f x = x ^ 1994 ∧ g x = 1993 * x * Real.sqrt (9 - x ^ 2) := by
  intro x
  have h1 : f x + g x = 1993 * x * Real.sqrt (9 - x ^ 2) + x ^ 1994 := hfg x
  have h2 : f (-x) + g (-x) = 1993 * (-x) * Real.sqrt (9 - (-x) ^ 2) + (-x) ^ 1994 := hfg (-x)
  have hf_x : f (-x) = f x := hf x
  have hg_x : g (-x) = -g x := hg x
  have h3 : f (-x) + g (-x) = f x - g x := by
    rw [hf_x, hg_x]
    ring
  have h4 : f x - g x = -1993 * x * Real.sqrt (9 - x ^ 2) + x ^ 1994 := by
    calc
      f x - g x = f (-x) + g (-x) := by rw [h3]
      _ = 1993 * (-x) * Real.sqrt (9 - (-x) ^ 2) + (-x) ^ 1994 := by rw [h2]
      _ = 1993 * (-x) * Real.sqrt (9 - x ^ 2) + x ^ 1994 := by
        ring_nf
        <;> simp [pow_even, sq]
        <;> ring
      _ = -1993 * x * Real.sqrt (9 - x ^ 2) + x ^ 1994 := by ring
  have h5 : 2 * f x = 2 * x ^ 1994 := by
    calc
      2 * f x = (f x + g x) + (f x - g x) := by ring
      _ = (1993 * x * Real.sqrt (9 - x ^ 2) + x ^ 1994) + (-1993 * x * Real.sqrt (9 - x ^ 2) + x ^ 1994) := by
        rw [h1, h4]
      _ = 2 * x ^ 1994 := by ring
  have h6 : 2 * g x = 2 * (1993 * x * Real.sqrt (9 - x ^ 2)) := by
    calc
      2 * g x = (f x + g x) - (f x - g x) := by ring
      _ = (1993 * x * Real.sqrt (9 - x ^ 2) + x ^ 1994) - (-1993 * x * Real.sqrt (9 - x ^ 2) + x ^ 1994) := by
        rw [h1, h4]
      _ = 2 * (1993 * x * Real.sqrt (9 - x ^ 2)) := by ring
  have h7 : f x = x ^ 1994 := by
    apply mul_left_cancel₀ (show (2 : ℝ) ≠ 0 by norm_num)
    linarith
  have h8 : g x = 1993 * x * Real.sqrt (9 - x ^ 2) := by
    apply mul_left_cancel₀ (show (2 : ℝ) ≠ 0 by norm_num)
    linarith
  exact ⟨h7, h8⟩
