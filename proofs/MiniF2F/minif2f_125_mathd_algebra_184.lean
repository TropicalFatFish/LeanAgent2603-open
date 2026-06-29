import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_184
  (a b : NNReal)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : (a^2) = 6*b)
  (h₂ : (a^2) = 54/b) :
  a = 3 * NNReal.sqrt 2 := by
  apply NNReal.eq
  have hbpos : (0 : ℝ) < b := by exact_mod_cast h₀.2
  have h1r : (a : ℝ)^2 = 6 * (b : ℝ) := by exact_mod_cast h₁
  have h2r : (a : ℝ)^2 = 54 / (b : ℝ) := by exact_mod_cast h₂
  have h2r' : (a : ℝ)^2 * (b : ℝ) = 54 := by
    field_simp [hbpos.ne'] at h2r ⊢
    linarith
  have hb : (b : ℝ) = 3 := by
    have : 6 * (b : ℝ)^2 = 54 := by nlinarith
    nlinarith [sq_nonneg ((b : ℝ) - 3), sq_nonneg ((b : ℝ) + 3), hbpos]
  have ha2 : (a : ℝ)^2 = 18 := by nlinarith
  exact (sq_eq_sq₀ (NNReal.coe_nonneg a) (by positivity : (0 : ℝ) ≤ ((3 * NNReal.sqrt 2 : NNReal) : ℝ))).mp (by
    calc
      (a : ℝ)^2 = 18 := ha2
      _ = ((3 * NNReal.sqrt 2 : NNReal) : ℝ)^2 := by
        have hsNN : ((3 * NNReal.sqrt 2 : NNReal)^2) = 18 := by
          rw [pow_two]
          ring_nf
          rw [NNReal.sq_sqrt]
          norm_num
        exact_mod_cast hsNN.symm)
