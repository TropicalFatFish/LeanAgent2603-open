import Mathlib

open Real

theorem u_math_526 {f : ℝ → ℝ} (hf : f = λ x => 20 * x - 2 * x ^ 2) (a : ℝ) (ha : a = 3) :
    (f (a + 0.1) - f a) / 0.1 = 7.8 ∧
    (f (a + 0.01) - f a) / 0.01 = 7.98 ∧
    (f (a + 0.001) - f a) / 0.001 = 7.998 ∧
    deriv f 3 = 8 := by
  have h1 : deriv f 3 = 8 := by
    rw [hf] at *
    rw [ha] at *

    have : deriv (fun x : ℝ => 20 * x - 2 * x ^ 2) 3 = 8 := by

      ring_nf
      <;>
      norm_num
      <;>
      rfl
    simpa [pow_two] using this

  have h2 : (f (a + 0.1) - f a) / 0.1 = 7.8 := by
    rw [hf] at *
    rw [ha] at *
    norm_num [pow_two]
    <;>
    linarith
  have h3 : (f (a + 0.01) - f a) / 0.01 = 7.98 := by
    rw [hf] at *
    rw [ha] at *
    norm_num [pow_two]
    <;>
    linarith
  have h4 : (f (a + 0.001) - f a) / 0.001 = 7.998 := by
    rw [hf] at *
    rw [ha] at *
    norm_num [pow_two]
    <;>
    linarith
  exact ⟨h2, h3, h4, h1⟩
