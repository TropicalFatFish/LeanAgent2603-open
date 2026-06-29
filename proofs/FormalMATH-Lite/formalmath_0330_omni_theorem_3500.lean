import Mathlib

theorem omni_theorem_3500 (x : ℕ) (h : x + 12 = 8 * (x - 2)) : x = 4 := by
  have h1 : x ≥ 2 := by
    by_contra hx

    have : x < 2 := by omega
    interval_cases x <;> simp_all [Nat.mul_sub_left_distrib]

  have : x = 4 := by
    have h2 : x - 2 + 2 = x := by
      have : 2 ≤ x := h1
      omega
    rw [← h2] at h
    ring_nf at h
    omega
  exact this
