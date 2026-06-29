import Mathlib

open Real

theorem omni_theorem_2378 (A B C D E F : EuclideanSpace ℝ (Fin 2))
    (h₀ : (MeasureTheory.volume (convexHull ℝ {E, F, C})).toReal = (5 / 6) * (MeasureTheory.volume (convexHull ℝ {A, E, C})).toReal)
    (h₁ : (MeasureTheory.volume (convexHull ℝ {A, E, C})).toReal = (4 / 5) * (MeasureTheory.volume (convexHull ℝ {A, D, C})).toReal)
    (h₂ : (MeasureTheory.volume (convexHull ℝ {A, D, C})).toReal = (2 / 3) * (MeasureTheory.volume (convexHull ℝ {A, B, C})).toReal)
    (h₃ : (MeasureTheory.volume (convexHull ℝ {A, B, C})).toReal = 20 * sqrt 3) :
    (MeasureTheory.volume (convexHull ℝ {E, F, C})).toReal = 80 * sqrt 3 / 9 := by
  rw [h₀, h₁, h₂, h₃]
  field_simp
  norm_num
