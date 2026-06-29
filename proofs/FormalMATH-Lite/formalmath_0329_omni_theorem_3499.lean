import Mathlib

open Real

theorem omni_theorem_3499 (total_prize : ℝ) (h : total_prize = 200)
    (jackie_prize : ℝ) (dale_natalia_prize : ℝ)
    (hj : jackie_prize = total_prize * 0.30)
    (hsplit : dale_natalia_prize = (total_prize - jackie_prize) * 0.15 / 2) :
    dale_natalia_prize = 10.50 := by
  rw [hsplit]
  rw [hj]
  rw [h]
  norm_num
