import Mathlib

def X : Finset ℕ := Finset.Icc 1 1995

def A (S : Finset ℕ) : Prop :=
  S ⊆ X ∧ ∀ x ∈ S, ∀ y ∈ S, x < y → y ≠ 15 * x

theorem quantitative_reasoning_zh_blue_352 :
    IsGreatest {n | ∃ S : Finset ℕ, A S ∧ S.card = n} 1870 := by
  constructor
  · let S : Finset ℕ := Finset.Icc 1 8 ∪ Finset.Icc 134 1995
    refine ⟨S, ?_, ?_⟩
    · constructor
      · intro a ha
        simp [S, X] at ha ⊢
        omega
      · intro x hx y hy hxy heq
        simp [S] at hx hy
        rcases hx with hx | hx <;> rcases hy with hy | hy <;> omega
    · have hdis : Disjoint (Finset.Icc 1 8) (Finset.Icc 134 1995) := by
        rw [Finset.disjoint_left]
        intro a ha hb
        simp at ha hb
        omega
      simp [S, Finset.card_union_of_disjoint hdis]
  · intro m hm
    rcases hm with ⟨S, hA, hcard⟩
    rw [← hcard]
    have hSX : S ⊆ X := hA.1
    let P : Finset ℕ := Finset.Icc 9 133
    let g : ℕ → ℕ := fun x => if x ∈ S then 15 * x else x
    have hmaps : Set.MapsTo g (P : Set ℕ) ((X \ S : Finset ℕ) : Set ℕ) := by
      intro x hx
      simp [P] at hx
      by_cases hxS : x ∈ S
      · have hnot : 15 * x ∉ S := by
          intro h15
          have hbad := hA.2 x hxS (15 * x) h15 (by omega)
          exact hbad rfl
        simp [g, hxS, X, hnot]
        omega
      · simp [g, hxS, X]
        omega
    have hinj : Set.InjOn g (P : Set ℕ) := by
      intro x hx y hy hxy
      simp [P] at hx hy
      by_cases hxS : x ∈ S <;> by_cases hyS : y ∈ S <;>
        simp [g, hxS, hyS] at hxy <;> omega
    have hcomp : P.card ≤ (X \ S).card :=
      Finset.card_le_card_of_injOn g hmaps hinj
    have hPcard : P.card = 125 := by
      simp [P]
    have hXcard : X.card = 1995 := by
      simp [X]
    have hsdiff : (X \ S).card + S.card = X.card :=
      Finset.card_sdiff_add_card_eq_card hSX
    omega
