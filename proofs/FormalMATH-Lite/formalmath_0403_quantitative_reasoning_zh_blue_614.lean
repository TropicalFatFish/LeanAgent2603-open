import Mathlib

theorem quantitative_reasoning_zh_blue_614 {f : ℕ → ℤ} (hf1 : f 1 = 1) (hfn : ∀ n > 0, f (n + 1) = 2 * f n + 1) :
    ∀ n > 0, f n = 2 ^ n - 1 := by
  intro n hn
  induction n with
  | zero =>
    exfalso
    linarith
  | succ n ih =>
    cases n <;> simp_all [pow_succ]
    all_goals norm_num
    all_goals ring
