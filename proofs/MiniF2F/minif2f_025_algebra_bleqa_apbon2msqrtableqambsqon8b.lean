import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_bleqa_apbon2msqrtableqambsqon8b
  (a b : ℝ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : b ≤ a) :
  (a + b) / 2 - Real.sqrt (a * b) ≤ (a - b)^2 / (8 * b) := by
  have h₂ : 0 < b := h₀.2
  have h₃ : 0 < a := h₀.1
  have h₄ : 0 < Real.sqrt a := Real.sqrt_pos.mpr h₃
  have h₅ : 0 < Real.sqrt b := Real.sqrt_pos.mpr h₂
  have h₆ : 0 < Real.sqrt a * Real.sqrt b := mul_pos h₄ h₅

  have h₇ : (a + b) / 2 - Real.sqrt (a * b) = (Real.sqrt a - Real.sqrt b)^2 / 2 := by
    have h₇a : 0 ≤ a := h₃.le
    have h₇b : 0 ≤ b := h₂.le
    have h₇c : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := by
      rw [Real.sqrt_mul h₇a]
    calc
      (a + b) / 2 - Real.sqrt (a * b) = (a + b) / 2 - Real.sqrt a * Real.sqrt b := by rw [h₇c]
      _ = (Real.sqrt a ^ 2 + Real.sqrt b ^ 2) / 2 - Real.sqrt a * Real.sqrt b := by
        have := Real.sq_sqrt h₇a
        have := Real.sq_sqrt h₇b
        simp [h₇c, h₇b, h₇a]
        <;> ring_nf
        <;> field_simp
      _ = ((Real.sqrt a - Real.sqrt b) ^ 2) / 2 := by
        ring_nf
        <;> field_simp

  have h₈ : (a - b) ^ 2 = (Real.sqrt a - Real.sqrt b) ^ 2 * (Real.sqrt a + Real.sqrt b) ^ 2 := by
    calc
      (a - b) ^ 2 = (Real.sqrt a ^ 2 - Real.sqrt b ^ 2) ^ 2 := by
        simp [Real.sq_sqrt h₃.le, Real.sq_sqrt h₂.le]
        <;> ring_nf
      _ = ((Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b)) ^ 2 := by ring_nf
      _ = (Real.sqrt a - Real.sqrt b) ^ 2 * (Real.sqrt a + Real.sqrt b) ^ 2 := by ring_nf

  rw [h₇, h₈]
  have h₁₀ : 0 < 8 * b := by positivity
  have h₁₁ : 0 < (Real.sqrt a + Real.sqrt b) := add_pos h₄ h₅
  have h₁₂ : 0 < (Real.sqrt a + Real.sqrt b) ^ 2 := pow_pos h₁₁ 2
  have h₁₃ : 4 * b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sqrt_nonneg a, Real.sqrt_nonneg b,
      Real.sq_sqrt h₃.le, Real.sq_sqrt h₂.le]
  field_simp [h₁₀.ne']
  have h₁₄ : (Real.sqrt a - Real.sqrt b) ^ 2 ≥ 0 := by positivity
  nlinarith [h₁₃, h₁₄]
