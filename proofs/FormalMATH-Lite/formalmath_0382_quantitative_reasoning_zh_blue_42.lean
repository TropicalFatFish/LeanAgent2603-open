import Mathlib

open Finset

def qr42ToRep (n : ℕ) (S : Set ℕ) : Set (Fin (n + 1)) :=
  {k | k.val + 1 ∈ S}

def qr42FromRep (n : ℕ) (T : Set (Fin (n + 1))) : Set ℕ :=
  {a | a ∈ Finset.Icc 1 (2 * n + 1) ∧
    ∃ k : Fin (n + 1), k ∈ T ∧
      (a = k.val + 1 ∨ a = 2 * n + 2 - (k.val + 1))}

lemma ncard_nonempty_subsets_fin (n : ℕ) :
    Set.ncard ({T : Set (Fin n) | T.Nonempty} : Set (Set (Fin n))) = 2 ^ n - 1 := by
  classical
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
  change Fintype.card {T : Set (Fin n) // T.Nonempty} = 2 ^ n - 1
  have hempty : Fintype.card {T : Set (Fin n) // ¬ T.Nonempty} = 1 := by
    let e : {T : Set (Fin n) // ¬ T.Nonempty} ≃ Unit :=
      { toFun := fun _ => ()
        invFun := fun _ => ⟨∅, by simp⟩
        left_inv := by
          intro T
          ext x
          exact (Set.not_nonempty_iff_eq_empty.mp T.2).symm ▸ Iff.rfl
        right_inv := by intro u; cases u; rfl }
    exact Fintype.card_congr e
  have hcompl := Fintype.card_subtype_compl (fun T : Set (Fin n) => T.Nonempty)
  rw [hempty, Fintype.card_set, Fintype.card_fin] at hcompl
  omega

lemma qr42_from_mem_valid {n : ℕ} {T : Set (Fin (n + 1))} (hT : T.Nonempty) :
    qr42FromRep n T ⊆ (Finset.Icc 1 (2 * n + 1) : Set ℕ) ∧
    (qr42FromRep n T).Nonempty ∧
    ∀ a ∈ qr42FromRep n T, (2 * n + 2 - a) ∈ qr42FromRep n T := by
  classical
  constructor
  · intro a ha
    exact ha.1
  constructor
  · rcases hT with ⟨k, hk⟩
    refine ⟨k.val + 1, ?_⟩
    constructor
    · simp only [mem_Icc]
      omega
    · exact ⟨k, hk, Or.inl rfl⟩
  · intro a ha
    rcases ha with ⟨haI, k, hkT, rfl | rfl⟩
    · constructor
      · simp only [mem_Icc]
        omega
      · exact ⟨k, hkT, Or.inr rfl⟩
    · constructor
      · simp only [mem_Icc] at haI ⊢
        omega
      · refine ⟨k, hkT, Or.inl ?_⟩
        omega

lemma qr42_to_nonempty {n : ℕ} {S : Set ℕ}
    (hS : S ⊆ (Finset.Icc 1 (2 * n + 1) : Set ℕ) ∧ S.Nonempty ∧
      ∀ a ∈ S, (2 * n + 2 - a) ∈ S) :
    (qr42ToRep n S).Nonempty := by
  classical
  rcases hS.2.1 with ⟨a, haS⟩
  have haI := hS.1 haS
  by_cases hle : a ≤ n + 1
  · have hpos : 1 ≤ a := (mem_Icc.mp haI).1
    refine ⟨⟨a - 1, by omega⟩, ?_⟩
    simpa [qr42ToRep, Nat.sub_add_cancel hpos] using haS
  · have hpS : 2 * n + 2 - a ∈ S := hS.2.2 a haS
    have hp_pos : 1 ≤ 2 * n + 2 - a := by
      have ha_le : a ≤ 2 * n + 1 := (mem_Icc.mp haI).2
      omega
    refine ⟨⟨(2 * n + 2 - a) - 1, by omega⟩, ?_⟩
    simpa [qr42ToRep, Nat.sub_add_cancel hp_pos] using hpS

lemma qr42_to_from {n : ℕ} (T : Set (Fin (n + 1))) :
    qr42ToRep n (qr42FromRep n T) = T := by
  classical
  ext k
  constructor
  · intro hk
    rcases hk with ⟨_, l, hlT, h | h⟩
    · have : l = k := by
        apply Fin.ext
        omega
      simpa [this] using hlT
    · have : l = k := by
        apply Fin.ext
        omega
      simpa [this] using hlT
  · intro hk
    dsimp [qr42ToRep, qr42FromRep]
    constructor
    · simp only [mem_Icc]
      omega
    · exact ⟨k, hk, Or.inl rfl⟩

lemma qr42_from_to {n : ℕ} {S : Set ℕ}
    (hS : S ⊆ (Finset.Icc 1 (2 * n + 1) : Set ℕ) ∧ S.Nonempty ∧
      ∀ a ∈ S, (2 * n + 2 - a) ∈ S) :
    qr42FromRep n (qr42ToRep n S) = S := by
  classical
  ext a
  constructor
  · intro ha
    rcases ha with ⟨haI, k, hkS, h | h⟩
    · simpa [qr42ToRep, h] using hkS
    · have hkS' : k.val + 1 ∈ S := by simpa [qr42ToRep] using hkS
      have hpS := hS.2.2 (k.val + 1) hkS'
      simpa [h] using hpS
  · intro haS
    have haI := hS.1 haS
    by_cases hle : a ≤ n + 1
    · have hpos : 1 ≤ a := (mem_Icc.mp haI).1
      refine ⟨haI, ⟨a - 1, by omega⟩, ?_, Or.inl ?_⟩
      · dsimp [qr42ToRep]
        simpa [Nat.sub_add_cancel hpos] using haS
      · change a = a - 1 + 1
        omega
    · have hpS : 2 * n + 2 - a ∈ S := hS.2.2 a haS
      have hp_pos : 1 ≤ 2 * n + 2 - a := by
        have ha_le : a ≤ 2 * n + 1 := (mem_Icc.mp haI).2
        omega
      refine ⟨haI, ⟨(2 * n + 2 - a) - 1, by omega⟩, ?_, Or.inr ?_⟩
      · dsimp [qr42ToRep]
        simpa [Nat.sub_add_cancel hp_pos] using hpS
      · change a = 2 * n + 2 - (((2 * n + 2 - a) - 1) + 1)
        omega

theorem quantitative_reasoning_zh_blue_42 {n : ℕ} (hn : 0 < n) :
    {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1 := by
  classical
  have _ : 0 < n := hn
  let A : Set (Set ℕ) :=
    {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}
  let B : Set (Set (Fin (n + 1))) := {T : Set (Fin (n + 1)) | T.Nonempty}
  change A.ncard = 2 ^ (n + 1) - 1
  calc
    A.ncard = B.ncard := by
      refine Set.ncard_congr (fun S hS => qr42ToRep n S) ?map ?inj ?surj
      · intro S hS
        exact qr42_to_nonempty hS
      · intro S₁ S₂ hS₁ hS₂ hEq
        change qr42ToRep n S₁ = qr42ToRep n S₂ at hEq
        have h1 := qr42_from_to (n := n) (S := S₁) hS₁
        have h2 := qr42_from_to (n := n) (S := S₂) hS₂
        rw [← h1, ← h2, hEq]
      · intro T hT
        refine ⟨qr42FromRep n T, qr42_from_mem_valid hT, ?_⟩
        exact qr42_to_from T
    _ = 2 ^ (n + 1) - 1 := ncard_nonempty_subsets_fin (n + 1)
