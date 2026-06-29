import Mathlib

def setOfInterests : Finset ℕ := {2, 3, 4, 6}

theorem omni_theorem_2745 (a b c : ℕ) (ha : a ∈ setOfInterests) (hb : b ∈ setOfInterests)
    (hc : c ∈ setOfInterests) (hdist : a ≠ b ∧ a ≠ c ∧ b ≠ c) (hsum : a + b + c = 11) :
    a * b * c = 36 := by
  simp only [setOfInterests] at ha hb hc

  have h₁ : a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 6 := by
    simp_all [Finset.mem_insert, Finset.mem_singleton]
  have h₂ : b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 6 := by
    simp_all [Finset.mem_insert, Finset.mem_singleton]
  have h₃ : c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 6 := by
    simp_all [Finset.mem_insert, Finset.mem_singleton]

  rcases h₁ with (rfl | rfl | rfl | rfl) <;>
  rcases h₂ with (rfl | rfl | rfl | rfl) <;>
  rcases h₃ with (rfl | rfl | rfl | rfl) <;>
  try {
    contradiction
  } <;>
  try {
    simp_all [hsum] <;>
    ring_nf at hsum ⊢ <;>
    linarith
  } <;>
  simp_all [hsum, hdist] <;>
  norm_num <;>
  linarith
