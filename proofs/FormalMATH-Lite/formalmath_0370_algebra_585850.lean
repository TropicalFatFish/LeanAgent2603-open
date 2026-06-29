import Mathlib

theorem algebra_585850 (x y z t : ℝ) :
    (|x| > |y - z + t| ∧ |y| > |x - z + t| ∧ |z| > |x - y + t| ∧ |t| > |x - y + z|) ↔ False := by
  constructor
  · intro h
    cases' abs_cases x with hx hx <;>
    try (cases' abs_cases (y - z + t) with hx1 hx1 <;>
         cases' abs_cases y with hy hy <;>
         cases' abs_cases (x - z + t) with hy1 hy1 <;>
         cases' abs_cases z with hz hz <;>
         cases' abs_cases (x - y + t) with hz1 hz1 <;>
         cases' abs_cases t with ht ht <;>
         cases' abs_cases (x - y + z) with ht1 ht1 <;>
         linarith)
  · intro h; contradiction
