import Mathlib

open Real

theorem u_math_661 {f : ℝ → ℝ}
    (hf : ∀ x y, f (y / x) = sqrt (x ^ 2 + y ^ 2) / x)
    (hx : 0 < x) : f x = sqrt (1 + x ^ 2) := by
  have h1 : f x = sqrt (x ^ 2 + (x ^ 2) ^ 2) / x := by
    have h1' : f ((x ^ 2) / x) = sqrt (x ^ 2 + (x ^ 2) ^ 2) / x := hf x (x ^ 2)
    have h2 : (x ^ 2) / x = x := by
      field_simp [hx.ne']
    rw [h2] at h1'
    exact h1'
  have h2 : sqrt (x ^ 2 + (x ^ 2) ^ 2) = x * sqrt (1 + x ^ 2) := by
    have h3 : x ^ 2 + (x ^ 2) ^ 2 = x ^ 2 * (1 + x ^ 2) := by ring
    rw [h3]
    have h4 : 0 < x ^ 2 := by positivity
    have h5 : 0 < 1 + x ^ 2 := by positivity
    have h6 : sqrt (x ^ 2 * (1 + x ^ 2)) = x * sqrt (1 + x ^ 2) := by
      rw [Real.sqrt_mul (le_of_lt h4)]
      rw [Real.sqrt_sq (by linarith)]
      <;> field_simp [hx.ne']
      <;> ring
    exact h6
  rw [h2] at h1
  field_simp [hx.ne'] at h1
  exact h1
