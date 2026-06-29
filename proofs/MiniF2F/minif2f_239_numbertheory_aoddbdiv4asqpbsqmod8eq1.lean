import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem numbertheory_aoddbdiv4asqpbsqmod8eq1
  (a : ℤ)
  (b : ℤ)
  (h₀ : Odd a)
  (h₁ : 4 ∣ b)
  (h₂ : b >= 0) :
  (a^2 + b^2) % 8 = 1 := by
  have h₄ : b^2 % 8 = 0 := by
    obtain ⟨c, he⟩ := h₁
    rw [he]
    ring_nf
    norm_num [Int.mul_emod, Int.emod_emod]

  have h₃ : a^2 % 8 = 1 := by
    cases h₀ with
    | intro k hk =>
      rw [hk] at *
      have h₅ : (2 * k + 1) % 2 = 1 := by norm_num
      have h₆ : (2 * k + 1) % 8 = 1 ∨ (2 * k + 1) % 8 = 3 ∨ (2 * k + 1) % 8 = 5 ∨ (2 * k + 1) % 8 = 7 := by
        omega
      rcases h₆ with (h₆ | h₆ | h₆ | h₆) <;>
        norm_num [pow_two, Int.mul_emod, h₆]

    <;> simp_all

  have h₇ : (a^2 + b^2) % 8 = 1 := by
    have h₈ : (a^2 + b^2) % 8 = (a^2 % 8 + b^2 % 8) % 8 := by
      rw [Int.add_emod]
    rw [h₈, h₃, h₄]
    norm_num

  exact h₇
