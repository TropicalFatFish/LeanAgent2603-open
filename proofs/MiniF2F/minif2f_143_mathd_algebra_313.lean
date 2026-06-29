import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_313
  (v i z : ℂ)
  (h₀ : v = i * z)
  (h₁ : v = 1 + Complex.I)
  (h₂ : z = 2 - Complex.I) :
  i = 1/5 + 3/5 * Complex.I := by
  have h₃ : i * (2 - Complex.I) = 1 + Complex.I := by
    calc
      i * (2 - Complex.I) = i * z := by rw [h₂]
      _ = v := by rw [h₀]
      _ = 1 + Complex.I := by rw [h₁]
  simp [Complex.ext_iff, Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.zero_im] at h₃
  have h₄ : (2 : ℝ) * Complex.re i + Complex.im i = 1 := by
    linarith
  have h₅ : -(Complex.re i) + (2 : ℝ) * Complex.im i = 1 := by
    linarith
  have h₆ : Complex.re i = (1 : ℝ) / 5 := by
    linarith
  have h₇ : Complex.im i = (3 : ℝ) / 5 := by
    linarith
  simp only [Complex.ext_iff, Complex.re, Complex.im, Complex.ofReal]
  constructor <;> simp [*] <;> norm_num
