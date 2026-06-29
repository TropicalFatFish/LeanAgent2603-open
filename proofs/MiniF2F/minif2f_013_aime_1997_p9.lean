import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1997_p9
  (a : ℝ)
  (h₀ : 0 < a)
  (h₁ : 1 / a - Int.floor (1 / a) = a^2 - Int.floor (a^2))
  (h₂ : 2 < a^2)
  (h₃ : a^2 < 3) :
  a^12 - 144 * (1 / a) = 233 := by
  have hfloor_sq : Int.floor (a ^ 2) = 2 := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num <;> linarith
  have hfloor_inv : Int.floor (1 / a) = 0 := by
    apply Int.floor_eq_iff.mpr
    constructor
    · norm_num
      positivity
    · norm_num
      have ha_gt_one : 1 < a := by nlinarith [h₀, h₂]
      simpa [one_div] using inv_lt_one_of_one_lt₀ ha_gt_one
  have hinv : 1 / a = a ^ 2 - 2 := by
    have h := h₁
    rw [hfloor_inv, hfloor_sq] at h
    norm_num at h ⊢
    linarith
  have hcubic : a ^ 3 = 2 * a + 1 := by
    have ha_ne : a ≠ 0 := by linarith
    field_simp [ha_ne] at hinv
    nlinarith
  have hquad : a ^ 2 = a + 1 := by
    have hfact : (a + 1) * (a ^ 2 - a - 1) = 0 := by
      nlinarith [hcubic]
    have hane : a + 1 ≠ 0 := by nlinarith [h₀]
    have hq0 : a ^ 2 - a - 1 = 0 := by
      exact (mul_eq_zero.mp hfact).resolve_left hane
    nlinarith
  have hinv' : 1 / a = a - 1 := by
    rw [hinv, hquad]
    ring
  have hpow : a ^ 12 = 144 * a + 89 := by
    have h3 : a ^ 3 = 2 * a + 1 := by
      calc
        a ^ 3 = a * a ^ 2 := by ring
        _ = a * (a + 1) := by rw [hquad]
        _ = a ^ 2 + a := by ring
        _ = (a + 1) + a := by rw [hquad]
        _ = 2 * a + 1 := by ring
    have h4 : a ^ 4 = 3 * a + 2 := by
      calc
        a ^ 4 = a * a ^ 3 := by ring
        _ = a * (2 * a + 1) := by rw [h3]
        _ = 2 * a ^ 2 + a := by ring
        _ = 2 * (a + 1) + a := by rw [hquad]
        _ = 3 * a + 2 := by ring
    have h5 : a ^ 5 = 5 * a + 3 := by
      calc
        a ^ 5 = a * a ^ 4 := by ring
        _ = a * (3 * a + 2) := by rw [h4]
        _ = 3 * a ^ 2 + 2 * a := by ring
        _ = 3 * (a + 1) + 2 * a := by rw [hquad]
        _ = 5 * a + 3 := by ring
    have h6 : a ^ 6 = 8 * a + 5 := by
      calc
        a ^ 6 = a * a ^ 5 := by ring
        _ = a * (5 * a + 3) := by rw [h5]
        _ = 5 * a ^ 2 + 3 * a := by ring
        _ = 5 * (a + 1) + 3 * a := by rw [hquad]
        _ = 8 * a + 5 := by ring
    have h7 : a ^ 7 = 13 * a + 8 := by
      calc
        a ^ 7 = a * a ^ 6 := by ring
        _ = a * (8 * a + 5) := by rw [h6]
        _ = 8 * a ^ 2 + 5 * a := by ring
        _ = 8 * (a + 1) + 5 * a := by rw [hquad]
        _ = 13 * a + 8 := by ring
    have h8 : a ^ 8 = 21 * a + 13 := by
      calc
        a ^ 8 = a * a ^ 7 := by ring
        _ = a * (13 * a + 8) := by rw [h7]
        _ = 13 * a ^ 2 + 8 * a := by ring
        _ = 13 * (a + 1) + 8 * a := by rw [hquad]
        _ = 21 * a + 13 := by ring
    have h9 : a ^ 9 = 34 * a + 21 := by
      calc
        a ^ 9 = a * a ^ 8 := by ring
        _ = a * (21 * a + 13) := by rw [h8]
        _ = 21 * a ^ 2 + 13 * a := by ring
        _ = 21 * (a + 1) + 13 * a := by rw [hquad]
        _ = 34 * a + 21 := by ring
    have h10 : a ^ 10 = 55 * a + 34 := by
      calc
        a ^ 10 = a * a ^ 9 := by ring
        _ = a * (34 * a + 21) := by rw [h9]
        _ = 34 * a ^ 2 + 21 * a := by ring
        _ = 34 * (a + 1) + 21 * a := by rw [hquad]
        _ = 55 * a + 34 := by ring
    have h11 : a ^ 11 = 89 * a + 55 := by
      calc
        a ^ 11 = a * a ^ 10 := by ring
        _ = a * (55 * a + 34) := by rw [h10]
        _ = 55 * a ^ 2 + 34 * a := by ring
        _ = 55 * (a + 1) + 34 * a := by rw [hquad]
        _ = 89 * a + 55 := by ring
    calc
      a ^ 12 = a * a ^ 11 := by ring
      _ = a * (89 * a + 55) := by rw [h11]
      _ = 89 * a ^ 2 + 55 * a := by ring
      _ = 89 * (a + 1) + 55 * a := by rw [hquad]
      _ = 144 * a + 89 := by ring
  calc
    a ^ 12 - 144 * (1 / a) = (144 * a + 89) - 144 * (a - 1) := by rw [hpow, hinv']
    _ = 233 := by ring
