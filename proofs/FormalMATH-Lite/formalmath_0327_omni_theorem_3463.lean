import Mathlib

theorem omni_theorem_3463 (a b c d e f : ℕ)
    (ha : a = 1 * 60 + 0) (hb : b = 2 * 60 + 20) (hc : c = 0 * 60 + 20)
    (hd : d = 1 * 60 + 45) (he : e = 0 * 60 + 20) (hf : f = 2 * 60 + 10) :
    a + b + c + d + e + f = 7 * 60 + 55 := by
  rw [ha, hb, hc, hd, he, hf] <;> simp <;> decide
