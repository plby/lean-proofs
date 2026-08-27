/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PairTwoAwayCutoff
import ErdosProblems.Erdos207.TwoAwayThreatWeight

/-!
# Pair-local genuinely two-away threats as a weight system

The designated missing triangle contains a fixed vertex pair and does not
share a pair with the fixed selector.  The latter exclusion removes precisely
the deletion targets already charged to the three pair-sharing classes.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- A two-away witness whose second missing triangle contains `P` and is not
already a pair-sharing target of `U`. -/
abbrev PairTwoAwayThreatWitness
    (V : Type*) [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (U : TripleOn V) (P : PairOn V) :=
  {z : TwoAwayThreatWitness V F U //
    P.1 ⊆ z.val.2.val ∧ z.val.2 ∉ triplesSharingPair U}

noncomputable instance instFintypePairTwoAwayThreatWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (U : TripleOn V) (P : PairOn V) :
    Fintype (PairTwoAwayThreatWitness V F U P) := by
  classical
  exact Fintype.ofFinite _

def pairTwoAwayThreatRemainder
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {U : TripleOn V} {P : PairOn V}
    (z : PairTwoAwayThreatWitness V F U P) : TripleSystemOn V :=
  twoAwayThreatRemainder z.1

def activePairTwoAwayThreatWitnesses
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (A : TripleSystemOn V)
    (U : TripleOn V) (P : PairOn V) :
    Finset (PairTwoAwayThreatWitness V F U P) :=
  (univ : Finset (PairTwoAwayThreatWitness V F U P)).filter fun z ↦
    pairTwoAwayThreatRemainder z ⊆ A

@[simp]
lemma mem_activePairTwoAwayThreatWitnesses_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A : TripleSystemOn V}
    {U : TripleOn V} {P : PairOn V}
    {z : PairTwoAwayThreatWitness V F U P} :
    z ∈ activePairTwoAwayThreatWitnesses F A U P ↔
      pairTwoAwayThreatRemainder z ⊆ A := by
  classical
  simp [activePairTwoAwayThreatWitnesses]

/-- The unavailability targets represented by pair-local witnesses. -/
def pairTwoAwayForbiddenTriangles
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (A : TripleSystemOn V)
    (U : TripleOn V) (P : PairOn V) : TripleSystemOn V :=
  universeTriplesContainingPair P.1 ∩
    nonPairTwoAwayForbiddenTriangles F A U

lemma image_activePairTwoAwayThreatWitnesses
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (A : TripleSystemOn V)
    (U : TripleOn V) (P : PairOn V) :
    (activePairTwoAwayThreatWitnesses F A U P).image
        (fun z ↦ z.val.val.2) =
      pairTwoAwayForbiddenTriangles F A U P := by
  classical
  ext T
  constructor
  · intro hT
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hT
    apply mem_inter.mpr
    refine ⟨mem_universeTriplesContainingPair_iff.mpr z.2.1, ?_⟩
    apply mem_sdiff.mpr
    refine ⟨?_, z.2.2⟩
    exact mem_twoAwayForbiddenTriangles_iff.mpr
      ⟨z.val.property.2.2.2, z.val.val.1, z.val.property.1,
        z.val.property.2.1, z.val.property.2.2.1,
        mem_activePairTwoAwayThreatWitnesses_iff.mp hz⟩
  · intro hT
    obtain ⟨hPT, hnonpair⟩ := mem_inter.mp hT
    obtain ⟨htwo, hnotshare⟩ := mem_sdiff.mp hnonpair
    obtain ⟨hTU, C, hCF, hTC, hUC, hrem⟩ :=
      mem_twoAwayForbiddenTriangles_iff.mp htwo
    let z₀ : TwoAwayThreatWitness V F U :=
      ⟨(C, T), hCF, hTC, hUC, hTU⟩
    let z : PairTwoAwayThreatWitness V F U P :=
      ⟨z₀, mem_universeTriplesContainingPair_iff.mp hPT, hnotshare⟩
    exact mem_image.mpr
      ⟨z, mem_activePairTwoAwayThreatWitnesses_iff.mpr (by
        simpa [pairTwoAwayThreatRemainder, z, z₀,
          twoAwayThreatRemainder] using hrem), rfl⟩

lemma card_pairTwoAwayForbiddenTriangles_le_witnesses
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A : TripleSystemOn V}
    {U : TripleOn V} {P : PairOn V} :
    (pairTwoAwayForbiddenTriangles F A U P).card ≤
      (activePairTwoAwayThreatWitnesses F A U P).card := by
  rw [← image_activePairTwoAwayThreatWitnesses]
  exact card_image_le

lemma available_pair_nonPairTwoAway_card_le_witnesses
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    (U : TripleOn V) (P : PairOn V) :
    (availableTrianglesContainingPair S P.1 ∩
      nonPairTwoAwayForbiddenTriangles F S.chosen U).card ≤
        (activePairTwoAwayThreatWitnesses F S.chosen U P).card := by
  apply (card_le_card ?_).trans card_pairTwoAwayForbiddenTriangles_le_witnesses
  intro T hT
  obtain ⟨hTpair, hTtwo⟩ := mem_inter.mp hT
  exact mem_inter.mpr
    ⟨mem_universeTriplesContainingPair_iff.mpr
      (mem_availableTrianglesContainingPair_iff.mp hTpair).2, hTtwo⟩

lemma selectedCount_pairTwoAwayThreatRemainder
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (A : TripleSystemOn V)
    (U : TripleOn V) (P : PairOn V) :
    selectedCount
      (fun z : PairTwoAwayThreatWitness V F U P ↦
        pairTwoAwayThreatRemainder z) A =
      ((activePairTwoAwayThreatWitnesses F A U P).card : ℝ≥0) := by
  classical
  unfold selectedCount activePairTwoAwayThreatWitnesses
  simp only [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, sum_filter]
  apply sum_congr rfl
  intro z _hz
  by_cases h : pairTwoAwayThreatRemainder z ⊆ A <;> simp [h]

lemma pairTwoAwayForbidden_count_le_selectedCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (A : TripleSystemOn V)
    (U : TripleOn V) (P : PairOn V) :
    ((pairTwoAwayForbiddenTriangles F A U P).card : ℝ≥0) ≤
      selectedCount
        (fun z : PairTwoAwayThreatWitness V F U P ↦
          pairTwoAwayThreatRemainder z) A := by
  rw [selectedCount_pairTwoAwayThreatRemainder]
  exact_mod_cast card_pairTwoAwayForbiddenTriangles_le_witnesses

lemma card_pairTwoAwayThreatRemainder_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {U : TripleOn V} {P : PairOn V} {k : ℕ}
    (hcard : ∀ C ∈ F, C.card ≤ k)
    (z : PairTwoAwayThreatWitness V F U P) :
    (pairTwoAwayThreatRemainder z).card ≤ k - 2 :=
  card_twoAwayThreatRemainder_le hcard z.1

/-- Generic moment estimate for one fixed selector and tracked pair. -/
theorem pairTwoAwayForbiddenMomentBound
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (R : Ω → TripleSystemOn V)
    (F : ForbiddenFamilyOn V) (U : TripleOn V) (P : PairOn V)
    (π : TripleOn V → ℝ≥0) (C κ : ℝ≥0) {k s : ℕ}
    (hcard : ∀ A ∈ F, A.card ≤ k)
    (hκ : HasExtensionBound
      (fun z : PairTwoAwayThreatWitness V F U P ↦
        pairTwoAwayThreatRemainder z) π κ)
    (hjoint : ∀ T : TripleSystemOn V, T.card ≤ s * (k - 2) →
      L.probability (fun ω ↦ T ⊆ R ω) ≤ C * setWeight π T) :
    L.expectation (fun ω ↦
      ((pairTwoAwayForbiddenTriangles F (R ω) U P).card : ℝ≥0) ^ s) ≤
      C * (((2 : ℝ≥0) ^ (s * (k - 2)) * κ) ^ s) := by
  calc
    L.expectation (fun ω ↦
        ((pairTwoAwayForbiddenTriangles F (R ω) U P).card : ℝ≥0) ^ s) ≤
      L.expectation (fun ω ↦
        (selectedCount
          (fun z : PairTwoAwayThreatWitness V F U P ↦
            pairTwoAwayThreatRemainder z) (R ω)) ^ s) := by
        apply FiniteLaw.expectation_mono
        intro ω
        exact pow_le_pow_left'
          (pairTwoAwayForbidden_count_le_selectedCount F (R ω) U P) s
    _ ≤ C * (((2 : ℝ≥0) ^ (s * (k - 2)) * κ) ^ s) := by
      apply configurationMomentBound L
        (fun z : PairTwoAwayThreatWitness V F U P ↦
          pairTwoAwayThreatRemainder z) R π C κ
      · exact card_pairTwoAwayThreatRemainder_le hcard
      · exact hκ
      · exact hjoint

end

end Erdos207
