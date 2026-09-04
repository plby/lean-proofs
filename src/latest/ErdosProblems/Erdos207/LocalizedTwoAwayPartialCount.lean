/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LocalizedTwoAwayFixedWeight
import ErdosProblems.Erdos207.AbsorberRootedCount

/-! # One inverse-ambient saving for partially exposed localized witnesses -/

namespace Erdos207

open Finset

noncomputable section

def localizedTwoAwayMissing
    {V : Type*} [Fintype V] [DecidableEq V] {F : ForbiddenFamilyOn V}
    {T : TripleOn V} {a b : V} {U : Finset V}
    (w : LocalizedTwoAwayWitness V F T a b U) : LocalizedUniverseTriplesThroughPair V a b U :=
  ⟨⟨w.1.1.2, mem_universeTriplesThroughPair_iff.mpr ⟨w.2.1, w.2.2.1⟩⟩, w.2.2.2⟩

abbrev LocalizedTwoAwayMissingCode
    (V : Type*) [Fintype V] [DecidableEq V]
    (T : TripleOn V) (a b : V) (U : Finset V) (R : TripleSystemOn V) :=
  {Z : LocalizedUniverseTriplesThroughPair V a b U // Z.1.1 ≠ T ∧ Z.1.1 ∉ R}

abbrev LocalizedTwoAwayRootCode
    (V : Type*) [Fintype V] [DecidableEq V] (F : ForbiddenFamilyOn V)
    (T : TripleOn V) (a b : V) (U : Finset V) (R : TripleSystemOn V) :=
  Σ Z : LocalizedTwoAwayMissingCode V T a b U R,
    familyExtensions F (insert T (insert Z.1.1.1 R))

def activeLocalizedTwoAwayRootCode
    {V : Type*} [Fintype V] [DecidableEq V] {F : ForbiddenFamilyOn V}
    {T : TripleOn V} {a b : V} {U : Finset V} {R : TripleSystemOn V}
    (w : ActiveLocalizedTwoAwayWitness V F T a b U R) :
    LocalizedTwoAwayRootCode V F T a b U R := by
  have hmissing : w.1.1.1.2 ∉ R := by
    intro hR
    have hmem := w.2 hR
    exact (mem_erase.mp (mem_erase.mp hmem).2).1 rfl
  refine ⟨⟨localizedTwoAwayMissing w.1, w.1.1.2.2.2.2, hmissing⟩,
    ⟨w.1.1.1.1, mem_familyExtensions_iff.mpr ⟨w.1.1.2.1, ?_⟩⟩⟩
  intro Z hZ
  rcases mem_insert.mp hZ with rfl | hZ
  · exact w.1.1.2.2.2.1
  · rcases mem_insert.mp hZ with rfl | hZ
    · exact w.1.1.2.2.1
    · exact mem_of_mem_erase (mem_of_mem_erase (w.2 hZ))

theorem activeLocalizedTwoAwayRootCode_injective
    {V : Type*} [Fintype V] [DecidableEq V] {F : ForbiddenFamilyOn V}
    {T : TripleOn V} {a b : V} {U : Finset V} {R : TripleSystemOn V} :
    Function.Injective (activeLocalizedTwoAwayRootCode :
      ActiveLocalizedTwoAwayWitness V F T a b U R → LocalizedTwoAwayRootCode V F T a b U R) := by
  intro w z h
  have hfamily := congrArg (fun v : LocalizedTwoAwayRootCode V F T a b U R ↦ v.2.1) h
  have hmissing := congrArg (fun v : LocalizedTwoAwayRootCode V F T a b U R ↦ v.1.1.1.1) h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext hfamily hmissing

theorem card_activeLocalizedTwoAway_partial_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j : ℕ) (B : TripleSystemOn V) (F : ForbiddenFamilyOn V)
    (hF : F ⊆ absorberInducedConfigurationsOn q j B)
    (T : TripleOn V) {a b : V} (hab : a ≠ b) (U : Finset V) (R : TripleSystemOn V)
    (hR : R.card < j - 4) :
    Fintype.card (ActiveLocalizedTwoAwayWitness V F T a b U R) ≤
      U.card * (pairExactBankExtensionCoefficient q B * (Fintype.card V + 1) ^ (j - R.card - 5)) := by
  classical
  by_cases hTR : T ∈ R
  · have he : IsEmpty (ActiveLocalizedTwoAwayWitness V F T a b U R) := ⟨fun w ↦ by
      have hmem := w.2 hTR
      exact (mem_erase.mp hmem).1 rfl⟩
    let := he
    rw [Fintype.card_eq_zero]
    exact Nat.zero_le _
  · have hcount := Fintype.card_le_of_injective
      (activeLocalizedTwoAwayRootCode : ActiveLocalizedTwoAwayWitness V F T a b U R →
        LocalizedTwoAwayRootCode V F T a b U R) activeLocalizedTwoAwayRootCode_injective
    have hmissing : Fintype.card (LocalizedTwoAwayMissingCode V T a b U R) ≤ U.card :=
      (Fintype.card_subtype_le _).trans (card_localizedUniverseTriplesThroughPair_le V hab U)
    have hsingle : ∀ Z : LocalizedTwoAwayMissingCode V T a b U R,
        (familyExtensions F (insert T (insert Z.1.1.1 R))).card ≤
          pairExactBankExtensionCoefficient q B * (Fintype.card V + 1) ^ (j - R.card - 5) := by
      intro Z
      have hTnot : T ∉ insert Z.1.1.1 R := by
        simp only [mem_insert, not_or]
        exact ⟨Z.2.1.symm, hTR⟩
      have hrootcard : (insert T (insert Z.1.1.1 R)).card = R.card + 2 := by
        rw [card_insert_of_notMem hTnot, card_insert_of_notMem Z.2.2]
      have hroot2 : 2 ≤ (insert T (insert Z.1.1.1 R)).card := by omega
      have hrootsmall : (insert T (insert Z.1.1.1 R)).card < j - 2 := by omega
      have hb := card_familyExtensions_absorberInduced_le_strong q j B
        (insert T (insert Z.1.1.1 R)) hroot2 hrootsmall
      have hsub : familyExtensions F (insert T (insert Z.1.1.1 R)) ⊆
          familyExtensions (absorberInducedConfigurationsOn q j B) (insert T (insert Z.1.1.1 R)) := by
        intro C hC
        exact mem_familyExtensions_iff.mpr
          ⟨hF (mem_familyExtensions_iff.mp hC).1, (mem_familyExtensions_iff.mp hC).2⟩
      have hexp : j - (insert T (insert Z.1.1.1 R)).card - 3 = j - R.card - 5 := by omega
      rw [hexp] at hb
      exact (card_le_card hsub).trans hb
    calc
      _ ≤ Fintype.card (LocalizedTwoAwayRootCode V F T a b U R) := hcount
      _ = ∑ Z : LocalizedTwoAwayMissingCode V T a b U R,
          (familyExtensions F (insert T (insert Z.1.1.1 R))).card := by
        simp only [LocalizedTwoAwayRootCode, Fintype.card_sigma, Fintype.card_coe]
      _ ≤ ∑ _Z : LocalizedTwoAwayMissingCode V T a b U R,
          pairExactBankExtensionCoefficient q B * (Fintype.card V + 1) ^ (j - R.card - 5) :=
        sum_le_sum fun Z _ ↦ hsingle Z
      _ = Fintype.card (LocalizedTwoAwayMissingCode V T a b U R) *
          (pairExactBankExtensionCoefficient q B * (Fintype.card V + 1) ^ (j - R.card - 5)) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hmissing

end

end Erdos207
