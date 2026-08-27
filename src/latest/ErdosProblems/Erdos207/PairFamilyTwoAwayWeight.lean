/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PairTwoAwayThreatWeight
import ErdosProblems.Erdos207.SupportBankWeightedBound

/-!
# Fixed-pair two-away witnesses in a uniform family

An Erdős configuration of order at least five is a packing.  Consequently,
after fixing a two-set `P`, a member of an exact bank class contains at most
one possible second missing triangle through `P`.  This removes the factor
equal to the family size in the ordinary two-away extension estimate.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- A fixed-size family witness whose second designated member contains the
tracked pair and is genuinely two-away from the first designated member. -/
abbrev PairFamilyTwoAwayWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : ForbiddenFamilyOn V) (U : TripleOn V) (P : PairOn V) :=
  {z : FamilyTwoAwayWitness G U //
    P.1 ⊆ z.missing.1 ∧ z.missing ∉ triplesSharingPair U}

noncomputable instance instFintypePairFamilyTwoAwayWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : ForbiddenFamilyOn V) (U : TripleOn V) (P : PairOn V) :
    Fintype (PairFamilyTwoAwayWitness G U P) := Fintype.ofFinite _

def pairFamilyTwoAwayRemainder
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : ForbiddenFamilyOn V} {U : TripleOn V} {P : PairOn V}
    (z : PairFamilyTwoAwayWitness G U P) : TripleSystemOn V :=
  familyTwoAwayRemainder z.1

abbrev ActivePairFamilyTwoAwayWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : ForbiddenFamilyOn V) (U : TripleOn V) (P : PairOn V)
    (A : TripleSystemOn V) :=
  {z : PairFamilyTwoAwayWitness G U P //
    A ⊆ pairFamilyTwoAwayRemainder z}

lemma pairFamilyTwoAwayWitness_ext
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : ForbiddenFamilyOn V} {U : TripleOn V} {P : PairOn V}
    {z w : PairFamilyTwoAwayWitness G U P}
    (hfamily : z.1.family = w.1.family)
    (hmissing : z.1.missing = w.1.missing) : z = w := by
  apply Subtype.ext
  cases hz : z.1 with
  | mk zfamily zfamilyMem zfixed zmissing zmissingMem zmissingNe =>
    cases hw : w.1 with
    | mk wfamily wfamilyMem wfixed wmissing wmissingMem wmissingNe =>
      simp only [hz, hw] at hfamily hmissing ⊢
      subst wfamily
      subst wmissing
      rfl

lemma pairFamilyTwoAwayRemainder_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : ForbiddenFamilyOn V} {U : TripleOn V} {P : PairOn V} {m : ℕ}
    (hcard : ∀ S ∈ G, S.card = m)
    (z : PairFamilyTwoAwayWitness G U P) :
    (pairFamilyTwoAwayRemainder z).card = m - 2 :=
  familyTwoAwayRemainder_card hcard z.1

/-- Exact constant-weight formula for fixed-pair witnesses. -/
lemma extensionWeight_pairFamilyTwoAway_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : ForbiddenFamilyOn V} {U : TripleOn V} {P : PairOn V} {m : ℕ}
    (hcard : ∀ S ∈ G, S.card = m)
    (p : ℝ≥0) (A : TripleSystemOn V) :
    extensionWeight
        (fun z : PairFamilyTwoAwayWitness G U P ↦
          pairFamilyTwoAwayRemainder z)
        (constantTripleWeight p) A =
      (Fintype.card (ActivePairFamilyTwoAwayWitness G U P A) : ℝ≥0) *
        p ^ (m - 2 - A.card) := by
  classical
  unfold extensionWeight
  calc
    (∑ z : PairFamilyTwoAwayWitness G U P,
        if A ⊆ pairFamilyTwoAwayRemainder z then
          setWeight (constantTripleWeight p)
            (pairFamilyTwoAwayRemainder z \ A) else 0) =
      ∑ z : PairFamilyTwoAwayWitness G U P,
        if A ⊆ pairFamilyTwoAwayRemainder z then
          p ^ (m - 2 - A.card) else 0 := by
      apply sum_congr rfl
      intro z _hz
      by_cases hA : A ⊆ pairFamilyTwoAwayRemainder z
      · rw [if_pos hA, if_pos hA, setWeight_constantTripleWeight,
          card_sdiff_of_subset hA, pairFamilyTwoAwayRemainder_card hcard]
      · simp [hA]
    _ = (Fintype.card (ActivePairFamilyTwoAwayWitness G U P A) : ℝ≥0) *
        p ^ (m - 2 - A.card) := by
      rw [Fintype.card_subtype, ← Finset.sum_filter]
      simp

/-- The family itself is a complete code for an active fixed-pair witness
when every member of the family is a packing. -/
def activePairFamilyTwoAwayEmbedding
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : ForbiddenFamilyOn V} {U : TripleOn V} {P : PairOn V}
    (A : TripleSystemOn V)
    (hpacking : ∀ S ∈ G, IsPackingOn S) :
    ActivePairFamilyTwoAwayWitness G U P A ↪
      familyExtensions G (insert U A) := by
  classical
  refine
    { toFun := fun z ↦ ⟨z.1.1.family, mem_familyExtensions_iff.mpr
        ⟨z.1.1.family_mem, ?_⟩⟩
      inj' := ?_ }
  · intro T hT
    rw [mem_insert] at hT
    rcases hT with rfl | hTA
    · exact z.1.1.fixed_mem
    · exact mem_of_mem_erase
        (mem_of_mem_erase (z.2 hTA))
  · intro z w hzw
    have hfamily : z.1.1.family = w.1.1.family :=
      congrArg (fun x ↦ x.1) hzw
    obtain ⟨x, y, hxy, hP⟩ := card_eq_two.mp P.2
    have hxP : x ∈ P.1 := by rw [hP]; simp
    have hyP : y ∈ P.1 := by rw [hP]; simp
    have hmissing : z.1.1.missing = w.1.1.missing := by
      apply hpacking z.1.1.family z.1.1.family_mem x y hxy
      · exact z.1.1.missing_mem
      · exact z.1.2.1 hxP
      · exact z.1.2.1 hyP
      · rw [hfamily]
        exact w.1.1.missing_mem
      · exact w.1.2.1 hxP
      · exact w.1.2.1 hyP
    apply Subtype.ext
    exact pairFamilyTwoAwayWitness_ext hfamily hmissing

lemma card_activePairFamilyTwoAwayWitness_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : ForbiddenFamilyOn V} {U : TripleOn V} {P : PairOn V}
    (A : TripleSystemOn V)
    (hpacking : ∀ S ∈ G, IsPackingOn S) :
    Fintype.card (ActivePairFamilyTwoAwayWitness G U P A) ≤
      (familyExtensions G (insert U A)).card :=
  by
    simpa using Fintype.card_le_of_embedding
      (activePairFamilyTwoAwayEmbedding A hpacking)

lemma exactBankOutsideExtensions_isPacking
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B R K S : TripleSystemOn V}
    (hr : 5 ≤ r) (hS : S ∈ exactBankOutsideExtensions r j B R K) :
    IsPackingOn S := by
  obtain ⟨_hScard, _hRS, E, hE, hEout, _hEin⟩ :=
    mem_exactBankOutsideExtensions_iff.mp hS
  apply (IsErdosConfig.isPackingOn hE hr).mono
  intro T hTS
  exact (mem_sdiff.mp (by rw [hEout]; exact hTS)).1

end

end Erdos207
