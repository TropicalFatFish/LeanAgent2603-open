import Mathlib

open Finset Real Nat Polynomial

set_option maxHeartbeats 800000
set_option exponentiation.threshold 3000

def b : ℕ → ℝ
| j => ((j : ℝ) ^ 2014) *
    ∏ i ∈ Icc (1 : ℕ) 2014 \ {j}, (((i : ℝ) ^ 2014 - (j : ℝ) ^ 2014))

lemma lagrange_sum_inv_mul_prod {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → ℝ)
    (hvs : Set.InjOn v (s : Set ι)) (hs : s.Nonempty)
    (h0 : ∀ i ∈ s, v i ≠ 0) :
    ∑ i ∈ s, (1 / (v i * ∏ j ∈ s.erase i, (v j - v i))) =
      1 / ∏ i ∈ s, v i := by
  classical
  let P : ℝ := ∏ i ∈ s, v i
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact prod_ne_zero_iff.mpr h0
  have hsum_basis_poly : ∑ i ∈ s, Lagrange.basis s v i = (1 : ℝ[X]) :=
    Lagrange.sum_basis hvs hs
  have hsum_basis_eval : ∑ i ∈ s, (Lagrange.basis s v i).eval 0 = (1 : ℝ) := by
    simpa [Polynomial.eval_finset_sum] using congrArg (fun p : ℝ[X] => p.eval 0) hsum_basis_poly
  have hbasis : ∀ i ∈ s,
      (Lagrange.basis s v i).eval 0 =
        P * (1 / (v i * ∏ j ∈ s.erase i, (v j - v i))) := by
    intro i hi
    have hv_i : v i ≠ 0 := h0 i hi
    have hden : ∀ j ∈ s.erase i, v j - v i ≠ 0 := by
      intro j hj
      rcases mem_erase.mp hj with ⟨hji, hjs⟩
      exact sub_ne_zero.mpr (fun h => hji (hvs hjs hi h))
    have hden' : ∀ j ∈ s.erase i, v i - v j ≠ 0 := by
      intro j hj
      exact sub_ne_zero.mpr (fun h => (hden j hj) (by linarith))
    have heval : (Lagrange.basis s v i).eval 0 =
        ∏ j ∈ s.erase i, (v j * (v j - v i)⁻¹) := by
      rw [Lagrange.basis, Polynomial.eval_prod]
      apply Finset.prod_congr rfl
      intro j hj
      rw [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C]
      field_simp [hden j hj, hden' j hj]
      ring
    rw [heval]
    simp_rw [div_eq_mul_inv]
    rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    dsimp [P]
    rw [← Finset.mul_prod_erase _ (fun j => v j) hi]
    field_simp [hv_i, hden]
  calc
    ∑ i ∈ s, 1 / (v i * ∏ j ∈ s.erase i, (v j - v i))
        = (1 / P) * ∑ i ∈ s, (Lagrange.basis s v i).eval 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [hbasis i hi]
          field_simp [hP_ne]
    _ = 1 / P := by simp [hsum_basis_eval]
    _ = 1 / ∏ i ∈ s, v i := rfl

theorem omni_theorem_1039 :
    ∑ j ∈ Icc (1 : ℕ) 2014, (1 / b j) = 1 / (Nat.factorial 2014) ^ 2014 := by
  classical
  let s : Finset ℕ := Icc (1 : ℕ) 2014
  let v : ℕ → ℝ := fun j => (j : ℝ) ^ 2014
  have hs : s.Nonempty := by
    dsimp [s]
    exact ⟨1, by simp⟩
  have h0 : ∀ i ∈ s, v i ≠ 0 := by
    intro i hi
    have hi1 : 1 ≤ i := (mem_Icc.mp hi).1
    dsimp [v]
    positivity
  have hinj : Set.InjOn v (s : Set ℕ) := by
    intro i hi j hj hij
    have hi1 : 1 ≤ i := (mem_Icc.mp hi).1
    have hj1 : 1 ≤ j := (mem_Icc.mp hj).1
    have hij_real_nat : ((i ^ 2014 : ℕ) : ℝ) = ((j ^ 2014 : ℕ) : ℝ) := by
      simpa [v, Nat.cast_pow] using hij
    have hij_nat : i ^ 2014 = j ^ 2014 :=
      Nat.cast_injective hij_real_nat
    exact Nat.pow_left_injective (by decide : 2014 ≠ 0) hij_nat
  have hlag :=
    lagrange_sum_inv_mul_prod (s := s) (v := v) hinj hs h0
  have hb_eq : ∀ j ∈ s, b j = v j * ∏ i ∈ s.erase j, (v i - v j) := by
    intro j hj
    dsimp [b, v, s]
    congr 2
    ext i
    simp [Finset.mem_erase, and_comm]
  have hsum :
      ∑ j ∈ s, (1 / b j) =
        ∑ j ∈ s, (1 / (v j * ∏ i ∈ s.erase j, (v i - v j))) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hb_eq j hj]
  have hprod : (∏ i ∈ s, v i) = (Nat.factorial 2014 : ℝ) ^ 2014 := by
    dsimp [s, v]
    rw [Finset.prod_pow]
    have hprod_nat : (∏ i ∈ Icc (1 : ℕ) 2014, i) = Nat.factorial 2014 := by
      rw [← Finset.Ico_succ_right_eq_Icc (a := (1 : ℕ)) (b := 2014)]
      exact Finset.prod_Ico_id_eq_factorial 2014
    have hprod_real : (∏ i ∈ Icc (1 : ℕ) 2014, (i : ℝ)) = (Nat.factorial 2014 : ℝ) := by
      rw [← Nat.cast_prod]
      rw [hprod_nat]
    rw [hprod_real]
  rw [hsum, hlag, hprod]
