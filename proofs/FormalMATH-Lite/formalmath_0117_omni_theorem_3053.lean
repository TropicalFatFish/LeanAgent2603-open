import Mathlib

def nabla (f g : ℝ) := f^2 - g^2

theorem omni_theorem_3053 {g : ℝ} (hg : g > 0) (h : nabla g 6 = 45) : g = 9 := by
  simp [nabla] at h
  have hg_sq : g^2 = 81 := by
    linarith
  have hg_eq_9 : g = 9 := by
    nlinarith [hg]
  exact hg_eq_9
