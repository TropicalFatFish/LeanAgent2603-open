import Mathlib

set_option maxHeartbeats 800000
set_option linter.unnecessarySeqFocus false

theorem omni_theorem_3620 (f : ℝ → ℝ) :
    (∀ x y, f x + f (y * f x + f y) = f (x + 2 * f y) + x * y) ↔ ∀ x, f x = x + 1 := by
  constructor
  · intro h
    let a : ℝ := f 0
    let c : ℝ := f a
    have hinj : Function.Injective f := by
      intro u v huv
      have hA0 : f (u + 2 * f u) + u * u = f (v + 2 * f u) + v * u := by
        calc
          f (u + 2 * f u) + u * u = f u + f (u * f u + f u) := by
            rw [(h u u).symm]
          _ = f v + f (u * f v + f u) := by rw [huv]
          _ = f (v + 2 * f u) + v * u := h v u
      have hB0 : f (u + 2 * f v) + u * v = f (v + 2 * f v) + v * v := by
        calc
          f (u + 2 * f v) + u * v = f u + f (v * f u + f v) := by
            rw [(h u v).symm]
          _ = f v + f (v * f v + f v) := by rw [huv]
          _ = f (v + 2 * f v) + v * v := h v v
      have hB : f (u + 2 * f u) + u * v = f (v + 2 * f u) + v * v := by
        simpa [huv] using hB0
      nlinarith
    have htrans : ∀ x, f (x + 2 * a) = f x + c := by
      intro x
      have hx := h x 0
      simpa [a, c] using hx.symm
    have ha_ne : a ≠ 0 := by
      intro ha0
      have hf0 : f 0 = 0 := by simpa [a] using ha0
      have hconst : ∀ y, f y = 0 := by
        intro y
        have hy := h 0 y
        have heq : f (f y) = f (2 * f y) := by
          simpa [hf0] using hy
        have harg := hinj heq
        linarith
      have h01 : f 0 = f 1 := by rw [hconst 0, hconst 1]
      have hzeroone : (0 : ℝ) = 1 := hinj h01
      norm_num at hzeroone
    have hc_ne : c ≠ 0 := by
      intro hc0
      have ht0 := htrans 0
      have heq : f (2 * a) = f 0 := by
        simpa [hc0] using ht0
      have harg := hinj heq
      have ha0 : a = 0 := by nlinarith
      exact ha_ne ha0
    have hshift : ∀ x y, f (y * f x + f y + c * y) = f (y * f x + f y) + 2 * a * y := by
      intro x y
      have hxy := h x y
      have hxy2 := h (x + 2 * a) y
      have hx : f (x + 2 * a) = f x + c := htrans x
      have hx2 : f (x + 2 * a + 2 * f y) = f (x + 2 * f y) + c := by
        have ht := htrans (x + 2 * f y)
        convert ht using 2 <;> ring_nf
      have hxy2' :
          f x + c + f (y * (f x + c) + f y) =
            f (x + 2 * f y) + c + (x + 2 * a) * y := by
        simpa [hx, hx2] using hxy2
      have hxy2'' :
          f x + c + f (y * f x + f y + c * y) =
            f (x + 2 * f y) + c + (x * y + 2 * a * y) := by
        convert hxy2' using 2 <;> ring_nf
      linarith
    have hc_sq : c ^ 2 = (2 * a) ^ 2 := by
      let y0 : ℝ := 2 * a / c
      let A : ℝ := y0 * f 0 + f y0
      have hcy : c * y0 = 2 * a := by
        dsimp [y0]
        field_simp [hc_ne]
      have hE := hshift 0 y0
      have hE' : f (A + 2 * a) = f A + 2 * a * y0 := by
        dsimp [A]
        simpa [hcy, add_comm, add_left_comm, add_assoc] using hE
      have hT : f (A + 2 * a) = f A + c := htrans A
      have hc_eq : c = 2 * a * y0 := by linarith
      have hc_mul : c * c = 4 * a * a := by
        dsimp [y0] at hc_eq
        field_simp [hc_ne] at hc_eq
        ring_nf at hc_eq ⊢
        linarith
      nlinarith
    have hc_cases : c = 2 * a ∨ c = -(2 * a) :=
      (sq_eq_sq_iff_eq_or_eq_neg.mp hc_sq)
    have hpos_a : c = 2 * a → a = 1 := by
      intro hcpos
      have hf0a : f 0 = a := rfl
      have hfa : f a = c := rfl
      have hf2a : f (2 * a) = 3 * a := by
        have ht := htrans 0
        have ht' : f (2 * a) = f 0 + c := by
          convert ht using 2 <;> ring_nf
        linarith only [ht', hf0a, hcpos]
      have hf3a : f (3 * a) = 4 * a := by
        have ht := htrans a
        have ht' : f (3 * a) = f a + c := by
          convert ht using 2 <;> ring_nf
        linarith only [ht', hfa, hcpos]
      have hf5a : f (5 * a) = 6 * a := by
        have ht := htrans (3 * a)
        have ht' : f (5 * a) = f (3 * a) + c := by
          convert ht using 2 <;> ring_nf
        linarith only [ht', hf3a, hcpos]
      have hf4a : f (4 * a) = 5 * a := by
        have ht := htrans (2 * a)
        have ht' : f (4 * a) = f (2 * a) + c := by
          convert ht using 2 <;> ring_nf
        linarith only [ht', hf2a, hcpos]
      have hf6a : f (6 * a) = 7 * a := by
        have ht := htrans (4 * a)
        have ht' : f (6 * a) = f (4 * a) + c := by
          convert ht using 2 <;> ring_nf
        linarith only [ht', hf4a, hcpos]
      have hmain : f (2 * a ^ 2 + 3 * a) = 6 * a := by
        have hp := h 0 (2 * a)
        have hp' : a + f ((2 * a) * a + f (2 * a)) = f (2 * f (2 * a)) := by
          simpa [a] using hp
        have hf6a' : f (2 * (3 * a)) = 7 * a := by
          convert hf6a using 2 <;> ring_nf
        rw [hf2a, hf6a'] at hp'
        ring_nf at hp' ⊢
        linarith
      have harg : 2 * a ^ 2 + 3 * a = 5 * a := by
        apply hinj
        rw [hmain, hf5a]
      have hfactor : a * (a - 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hfactor with ha0 | ha1
      · exact False.elim (ha_ne ha0)
      · linarith
    have hneg_false : c = -(2 * a) → False := by
      intro hcneg
      have hf0a : f 0 = a := rfl
      have hfa : f a = c := rfl
      have hf2a : f (2 * a) = -a := by
        have ht := htrans 0
        have ht' : f (2 * a) = f 0 + c := by
          convert ht using 2 <;> ring_nf
        linarith only [ht', hf0a, hcneg]
      have hfneg2a : f (-2 * a) = 3 * a := by
        have ht := htrans (-2 * a)
        have ht' : f 0 = f (-2 * a) + c := by
          convert ht using 2 <;> ring_nf
        linarith only [ht', hf0a, hcneg]
      have hfneg3a : f (-3 * a) = 2 * a := by
        have ht1 := htrans (-3 * a)
        have ht1' : f (-a) = f (-3 * a) + c := by
          convert ht1 using 2 <;> ring_nf
        have ht2 := htrans (-a)
        have ht2' : f a = f (-a) + c := by
          convert ht2 using 2 <;> ring_nf
        linarith only [ht1', ht2', hfa, hcneg]
      have hmain : f (2 * a ^ 2 - a) = 2 * a := by
        have hp := h 0 (2 * a)
        have hp' : a + f ((2 * a) * a + f (2 * a)) = f (2 * f (2 * a)) := by
          simpa [a] using hp
        have hfneg2a' : f (2 * (-a)) = 3 * a := by
          convert hfneg2a using 2 <;> ring_nf
        rw [hf2a, hfneg2a'] at hp'
        ring_nf at hp' ⊢
        linarith
      have harg : 2 * a ^ 2 - a = -3 * a := by
        apply hinj
        rw [hmain, hfneg3a]
      have hfactor : a * (a + 1) = 0 := by nlinarith
      have ha_neg_one : a = -1 := by
        rcases mul_eq_zero.mp hfactor with ha0 | ha1
        · exact False.elim (ha_ne ha0)
        · linarith
      have hc_two : c = 2 := by nlinarith only [hcneg, ha_neg_one]
      have hf0 : f 0 = -1 := by simpa [a] using ha_neg_one
      have hfneg1 : f (-1) = 2 := by
        rw [ha_neg_one, hc_two] at hfa
        exact hfa
      have hf1 : f 1 = 0 := by
        have ht := htrans 1
        rw [ha_neg_one, hc_two] at ht
        norm_num at ht
        linarith only [ht, hfneg1]
      have hf3 : f 3 = -2 := by
        have ht := htrans 3
        rw [ha_neg_one, hc_two] at ht
        norm_num at ht
        linarith only [ht, hf1]
      have hf2 : f 2 = -3 := by
        have ht := htrans 2
        rw [ha_neg_one, hc_two] at ht
        norm_num at ht
        linarith only [ht, hf0]
      have hf4 : f 4 = -5 := by
        have ht := htrans 4
        rw [ha_neg_one, hc_two] at ht
        norm_num at ht
        linarith only [ht, hf2]
      have hp := h 0 (-1)
      rw [hf0, hfneg1] at hp
      norm_num at hp
      rw [hf3, hf4] at hp
      norm_num at hp
    have ha_one : a = 1 := by
      rcases hc_cases with hcpos | hcneg
      · exact hpos_a hcpos
      · exact False.elim (hneg_false hcneg)
    have hc_two : c = 2 := by
      rcases hc_cases with hcpos | hcneg
      · have ha1 := hpos_a hcpos
        linarith only [ha1, hcpos]
      · exact False.elim (hneg_false hcneg)
    have hf0 : f 0 = 1 := by simpa [a] using ha_one
    have hf1 : f 1 = 2 := by
      have hfa : f a = c := rfl
      rw [ha_one, hc_two] at hfa
      exact hfa
    have htrans12 : ∀ x, f (x + 2) = f x + 2 := by
      intro x
      have ht := htrans x
      rw [ha_one, hc_two] at ht
      simpa using ht
    have hfcomp : ∀ x, f (f x) = x + 2 := by
      intro x
      have hp := h x 1
      have hfx2 : f (f x + 2) = f (f x) + 2 := htrans12 (f x)
      have hx4 : f (x + 4) = f x + 4 := by
        have h1 := htrans12 x
        have h2 := htrans12 (x + 2)
        have h2' : f (x + 4) = f (x + 2) + 2 := by
          convert h2 using 2 <;> ring_nf
        linarith
      have hp' : f x + f (f x + 2) = f (x + 4) + x := by
        rw [hf1] at hp
        ring_nf at hp ⊢
        exact hp
      rw [hfx2, hx4] at hp'
      ring_nf at hp' ⊢
      linarith
    have hsurj : Function.Surjective f := by
      intro z
      refine ⟨f (z - 2), ?_⟩
      have hz := hfcomp (z - 2)
      ring_nf at hz ⊢
      exact hz
    have hshift_all : ∀ z d, f (z + d) = f z + d := by
      intro z d
      by_cases hd : d = 0
      · simp [hd]
      · let y : ℝ := d / 2
        have hy_ne : y ≠ 0 := by
          intro hy0
          apply hd
          have hy0' : d / 2 = 0 := by simpa [y] using hy0
          linarith
        rcases hsurj ((z - f y) / y) with ⟨x, hx⟩
        have hbase : y * f x + f y = z := by
          rw [hx]
          field_simp [hy_ne]
          ring_nf
        have hE := hshift x y
        have hE' : f (y * f x + f y + 2 * y) = f (y * f x + f y) + 2 * y := by
          rw [ha_one, hc_two] at hE
          simpa using hE
        have hdy : 2 * y = d := by
          dsimp [y]
          ring
        rw [hbase, hdy] at hE'
        exact hE'
    intro x
    have hx := hshift_all 0 x
    rw [hf0] at hx
    simpa [add_comm] using hx
  · intro hf x y
    simp [hf]
    ring
