import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_227
  (x y n : ℕ+)
  (h₀ : ↑x / (4:ℝ) + y / 6 = (x + y) / n) :
  n = 5 := by
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast x.property
  have hypos : (0 : ℝ) < (y : ℝ) := by exact_mod_cast y.property
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast n.property
  have hEq :
      (n : ℝ) * (3 * (x : ℝ) + 2 * (y : ℝ)) =
        12 * ((x : ℝ) + (y : ℝ)) := by
    field_simp [ne_of_gt hnpos] at h₀
    ring_nf at h₀ ⊢
    nlinarith
  rcases lt_trichotomy (n : ℕ) 5 with hnlt | hneq | hngt
  · have hnle4 : (n : ℝ) ≤ 4 := by
      exact_mod_cast Nat.le_of_lt_succ hnlt
    have :
        (n : ℝ) * (3 * (x : ℝ) + 2 * (y : ℝ)) <
          12 * ((x : ℝ) + (y : ℝ)) := by
      nlinarith
    nlinarith
  · apply Subtype.ext
    exact hneq
  · have hnge6 : (6 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hngt
    have :
        12 * ((x : ℝ) + (y : ℝ)) <
          (n : ℝ) * (3 * (x : ℝ) + 2 * (y : ℝ)) := by
      nlinarith
    nlinarith
