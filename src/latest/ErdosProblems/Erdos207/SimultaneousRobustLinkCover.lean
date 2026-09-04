/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SimultaneousLinkCoverLawDynamic
import ErdosProblems.Erdos207.SimultaneousRobustHallSampling
import ErdosProblems.Erdos207.TwoSidedRandomLinkMatchingCover

/-!
# Robust simultaneous link samples give a safe cover

The probabilistic input to the outer-link stage is most naturally expressed
as a degree bound.  A sampled pair is bad at the current state when its
triangle either repeats an already covered pair or participates in a
forbidden configuration contained in the current packing together with the
local sampled reservoir.  If the bad-pair relation has bounded degree on
both sides, two-sided robust Hall supplies a safe perfect matching.

This file proves that deterministic implication and then feeds it into the
dynamic simultaneous-link iterator.  Thus subsequent probability estimates
only have to establish simultaneous robustness and the two bad-degree
bounds.
-/

namespace Erdos207

open Finset

noncomputable section

/-- The local triangle reservoir belonging to one chosen bipartite link. -/
def bipartiteLinkReservoir
    {V : Type*} [DecidableEq V] (K : BipartiteLink V)
    (R : Finset (↥K.left × ↥K.right)) : TripleSystemOn V :=
  linkReservoirTriangles K.center K.leftEmbedding K.rightEmbedding
    K.center_ne_left K.center_ne_right K.left_ne_right R

/-- A sampled pair which cannot safely be used at the current state. -/
def bipartiteLinkBadPair
    {V : Type*} [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V)
    (K : BipartiteLink V) (R : Finset (↥K.left × ↥K.right))
    (a : ↥K.left) (b : ↥K.right) : Prop :=
  let T := linkMatchingTriple K.center K.leftEmbedding K.rightEmbedding
    K.center_ne_left K.center_ne_right K.left_ne_right a b
  ¬ TriangleAvoidsGraph (coveredGraph P) T ∨
    ParticipatesForbidden F P (bipartiteLinkReservoir K R) T

noncomputable instance bipartiteLinkBadPair.instDecidableRel
    {V : Type*} [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V)
    (K : BipartiteLink V) (R : Finset (↥K.left × ↥K.right)) :
    DecidableRel (bipartiteLinkBadPair F P K R) := by
  intro a b
  exact Classical.propDecidable _

/-- Only current link candidates matter to robust Hall.  Filtering the
unsafe-pair relation by the ambient candidate relation is essential: pairs
which were never candidates are irrelevant to the matching and must not be
charged to the deletion-degree budget. -/
def bipartiteLinkRelevantBadPair
    {V : Type*} [DecidableEq V]
    {K : BipartiteLink V}
    (r : ↥K.left → ↥K.right → Prop)
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V)
    (R : Finset (↥K.left × ↥K.right))
    (a : ↥K.left) (b : ↥K.right) : Prop :=
  r a b ∧ bipartiteLinkBadPair F P K R a b

noncomputable instance bipartiteLinkRelevantBadPair.instDecidableRel
    {V : Type*} [DecidableEq V]
    {K : BipartiteLink V}
    (r : ↥K.left → ↥K.right → Prop) [DecidableRel r]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V)
    (R : Finset (↥K.left × ↥K.right)) :
    DecidableRel (bipartiteLinkRelevantBadPair r F P R) := by
  intro a b
  exact Classical.propDecidable _

/-- A two-sided robust local sample, after deleting exactly the unsafe
pairs, gives the state-dependent extension required by the cover iterator. -/
theorem exists_reservoirLinkCover_of_twoSidedRobustSample
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (available P : TripleSystemOn V)
    (K : BipartiteLink V)
    (r : ↥K.left → ↥K.right → Prop) [DecidableRel r]
    (Delta : ℕ) (R : Finset (↥K.left × ↥K.right))
    (hrobust : IsTwoSidedRobustMatchingSample r Delta R)
    (hPpacking : IsPackingOn P) (hPavoid : AvoidsForbidden P F)
    (havailable : ∀ a b, r a b → (a, b) ∈ R →
      linkMatchingTriple K.center K.leftEmbedding K.rightEmbedding
        K.center_ne_left K.center_ne_right K.left_ne_right a b ∈ available)
    (hleftBad : ∀ a,
      (deletedNeighbors
        (bipartiteLinkRelevantBadPair r F P R) a).card ≤ Delta)
    (hrightBad : ∀ b,
      (deletedNeighbors
        (transposeRelation
          (bipartiteLinkRelevantBadPair r F P R)) b).card ≤ Delta) :
    ∃ M : TripleSystemOn V,
      M ⊆ available ∧ M ⊆ bipartiteLinkReservoir K R ∧
      Disjoint P M ∧ IsPackingOn (P ∪ M) ∧
      AvoidsForbidden (P ∪ M) F ∧ CoversBipartiteLink K M := by
  classical
  let sampled : ↥K.left → ↥K.right → Prop :=
    fun a b ↦ r a b ∧ (a, b) ∈ R
  let : DecidableRel sampled := by
    intro a b
    exact Classical.propDecidable _
  have hmatching : ∀ (deleted : ↥K.left → ↥K.right → Prop)
      [DecidableRel deleted],
      (∀ a, (deletedNeighbors deleted a).card ≤ Delta) →
      (∀ b, (deletedNeighbors (transposeRelation deleted) b).card ≤
        Delta) →
      ∃ f : ↥K.left → ↥K.right, Function.Bijective f ∧
        ∀ a, sampled a (f a) ∧ (a, f a) ∈ R ∧
          ¬ deleted a (f a) := by
    intro deleted _ hleft hright
    obtain ⟨f, hfbij, hf⟩ := hrobust deleted hleft hright
    exact ⟨f, hfbij, fun a ↦ ⟨⟨(hf a).1, (hf a).2.1⟩,
      (hf a).2.1, (hf a).2.2⟩⟩
  obtain ⟨M, hMavailable, hMreservoir, hPMdisjoint, hPMpacking,
      hPMavoid, hleftCover, hrightCover⟩ :=
    exists_safe_linkMatchingTriangles_of_twoSided_sample
      K.center K.leftEmbedding K.rightEmbedding K.center_ne_left
      K.center_ne_right K.left_ne_right F P available sampled Delta R
      hmatching hPpacking hPavoid
      (by
        intro a b hab
        exact havailable a b hab.1 hab.2)
      (bipartiteLinkRelevantBadPair r F P R)
      (by
        intro a b hr _hab hnotBad
        have hnotUnsafe : ¬ bipartiteLinkBadPair F P K R a b := by
          intro hunsafe
          exact hnotBad ⟨hr.1, hunsafe⟩
        exact Classical.not_not.mp (not_or.mp hnotUnsafe).1)
      hleftBad hrightBad
      (by
        intro a b hr _hab hnotBad
        have hnotUnsafe : ¬ bipartiteLinkBadPair F P K R a b := by
          intro hunsafe
          exact hnotBad ⟨hr.1, hunsafe⟩
        exact (not_or.mp hnotUnsafe).2)
  exact ⟨M, hMavailable, hMreservoir, hPMdisjoint, hPMpacking, hPMavoid,
    ⟨fun x hx ↦ hleftCover ⟨x, hx⟩,
      fun x hx ↦ hrightCover ⟨x, hx⟩⟩⟩

/-- The local reservoir of a center is a subfamily of the single global
simultaneous reservoir. -/
theorem bipartiteLinkReservoir_simultaneous_subset
    {O V : Type*} [Fintype O] [DecidableEq O]
    [Fintype V] [DecidableEq V]
    (U : Finset V) (center : O ↪ V) (K : O → BipartiteLink V)
    (hcenter : ∀ o, (K o).center = center o)
    (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U)
    (hright : ∀ o, (K o).right ⊆ U)
    (omega : SimultaneousLinkPair O V K → Bool) (o : O) :
    bipartiteLinkReservoir (K o)
        (simultaneousLinkSelectedPairs K omega o) ⊆
      simultaneousLinkReservoir U center K hcenter hout hleft hright
        omega := by
  classical
  intro T hT
  obtain ⟨ab, hab, rfl⟩ := mem_image.mp hT
  rw [simultaneousLinkReservoir, encodedReservoir]
  apply mem_map.mpr
  refine ⟨⟨o, ab⟩, ?_, rfl⟩
  exact FiniteLaw.mem_selectedByBits_iff.mpr
    (mem_simultaneousLinkSelectedPairs_iff.mp hab)

/-- Candidate pair-conflicts at one fixed left endpoint. -/
def bipartiteLinkRelevantPairConflictNeighbors
    {V : Type*} [DecidableEq V]
    {K : BipartiteLink V}
    (r : ↥K.left → ↥K.right → Prop)
    (P : TripleSystemOn V) (a : ↥K.left) :
    Finset ↥K.right := by
  classical
  exact univ.filter fun b ↦ r a b ∧
    ¬ TriangleAvoidsGraph (coveredGraph P)
      (linkMatchingTriple K.center K.leftEmbedding K.rightEmbedding
        K.center_ne_left K.center_ne_right K.left_ne_right a b)

/-- Candidate pair-conflicts at one fixed right endpoint. -/
def bipartiteLinkRelevantRightPairConflictNeighbors
    {V : Type*} [DecidableEq V]
    {K : BipartiteLink V}
    (r : ↥K.left → ↥K.right → Prop)
    (P : TripleSystemOn V) (b : ↥K.right) :
    Finset ↥K.left := by
  classical
  exact univ.filter fun a ↦ r a b ∧
    ¬ TriangleAvoidsGraph (coveredGraph P)
      (linkMatchingTriple K.center K.leftEmbedding K.rightEmbedding
        K.center_ne_left K.center_ne_right K.left_ne_right a b)

/-- If every candidate avoids the historical packing, a conflict with the
current packing is already a conflict with a newly added triangle. -/
lemma bipartiteLinkRelevantPairConflictNeighbors_subset_sdiff
    {V : Type*} [Fintype V] [DecidableEq V]
    {K : BipartiteLink V}
    (r : ↥K.left → ↥K.right → Prop)
    (Pbase P : TripleSystemOn V)
    (hbaseSafe : ∀ a b, r a b →
      TriangleAvoidsGraph (coveredGraph Pbase)
        (linkMatchingTriple K.center K.leftEmbedding K.rightEmbedding
          K.center_ne_left K.center_ne_right K.left_ne_right a b))
    (a : ↥K.left) :
    bipartiteLinkRelevantPairConflictNeighbors r P a ⊆
      linkPairConflictNeighbors (P \ Pbase) K a := by
  classical
  intro b hb
  have hb' := mem_filter.mp hb
  apply mem_filter.mpr
  refine ⟨mem_univ b, ?_⟩
  intro hnewSafe
  apply hb'.2.2
  intro u hu v hv huv hcovered
  obtain ⟨T, hTP, huT, hvT, hne⟩ := coveredGraph_adj.mp hcovered
  by_cases hTbase : T ∈ Pbase
  · exact hbaseSafe a b hb'.2.1 u hu v hv huv
      (coveredGraph_adj.mpr ⟨T, hTbase, huT, hvT, hne⟩)
  · exact hnewSafe u hu v hv huv
      (coveredGraph_adj.mpr
        ⟨T, mem_sdiff.mpr ⟨hTP, hTbase⟩, huT, hvT, hne⟩)

/-- Right-oriented counterpart of
`bipartiteLinkRelevantPairConflictNeighbors_subset_sdiff`. -/
lemma bipartiteLinkRelevantRightPairConflictNeighbors_subset_sdiff
    {V : Type*} [Fintype V] [DecidableEq V]
    {K : BipartiteLink V}
    (r : ↥K.left → ↥K.right → Prop)
    (Pbase P : TripleSystemOn V)
    (hbaseSafe : ∀ a b, r a b →
      TriangleAvoidsGraph (coveredGraph Pbase)
        (linkMatchingTriple K.center K.leftEmbedding K.rightEmbedding
          K.center_ne_left K.center_ne_right K.left_ne_right a b))
    (b : ↥K.right) :
    bipartiteLinkRelevantRightPairConflictNeighbors r P b ⊆
      linkRightPairConflictNeighbors (P \ Pbase) K b := by
  classical
  intro a ha
  have ha' := mem_filter.mp ha
  apply mem_filter.mpr
  refine ⟨mem_univ a, ?_⟩
  intro hnewSafe
  apply ha'.2.2
  intro u hu v hv huv hcovered
  obtain ⟨T, hTP, huT, hvT, hne⟩ := coveredGraph_adj.mp hcovered
  by_cases hTbase : T ∈ Pbase
  · exact hbaseSafe a b ha'.2.1 u hu v hv huv
      (coveredGraph_adj.mpr ⟨T, hTbase, huT, hvT, hne⟩)
  · exact hnewSafe u hu v hv huv
      (coveredGraph_adj.mpr
        ⟨T, mem_sdiff.mpr ⟨hTP, hTbase⟩, huT, hvT, hne⟩)

/-- The relevant bad neighbors are contained in the union of relevant
pair-conflicts and all forbidden-participation conflicts. -/
lemma deletedNeighbors_bipartiteLinkRelevantBadPair_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    {K : BipartiteLink V}
    (r : ↥K.left → ↥K.right → Prop) [DecidableRel r]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V)
    (R : Finset (↥K.left × ↥K.right))
    (a : ↥K.left) :
    deletedNeighbors (bipartiteLinkRelevantBadPair r F P R) a ⊆
      bipartiteLinkRelevantPairConflictNeighbors r P a ∪
        linkForbiddenParticipantNeighbors F P K R a := by
  classical
  intro b hb
  rw [mem_deletedNeighbors_iff] at hb
  obtain ⟨hr, hconflict | hforbidden⟩ := hb
  · apply mem_union_left
    simpa only [bipartiteLinkRelevantPairConflictNeighbors, mem_filter,
      mem_univ, true_and] using And.intro hr hconflict
  · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, hforbidden⟩)

/-- Right-oriented counterpart of
`deletedNeighbors_bipartiteLinkRelevantBadPair_subset`. -/
lemma deletedNeighbors_transpose_bipartiteLinkRelevantBadPair_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    {K : BipartiteLink V}
    (r : ↥K.left → ↥K.right → Prop) [DecidableRel r]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V)
    (R : Finset (↥K.left × ↥K.right))
    (b : ↥K.right) :
    deletedNeighbors
        (transposeRelation (bipartiteLinkRelevantBadPair r F P R)) b ⊆
      bipartiteLinkRelevantRightPairConflictNeighbors r P b ∪
        linkRightForbiddenParticipantNeighbors F P K R b := by
  classical
  intro a ha
  rw [mem_deletedNeighbors_iff] at ha
  obtain ⟨hr, hconflict | hforbidden⟩ := ha
  · apply mem_union_left
    simpa only [bipartiteLinkRelevantRightPairConflictNeighbors, mem_filter,
      mem_univ, true_and] using And.intro hr hconflict
  · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, hforbidden⟩)

/-- Covered-degree and rooted-active cutoffs imply both oriented degree
bounds for the exact unsafe-pair relation. -/
theorem bipartiteLinkBadDegree_of_cutoffs
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V)
    (K : BipartiteLink V) (R : Finset (↥K.left × ↥K.right))
    (Delta degreeCutoff rootCutoff familyCutoff : ℕ)
    (hfamily : ∀ C ∈ F, C.card ≤ familyCutoff)
    (hleaveLeft : ∀ a : ↥K.left,
      (leaveGraph P).Adj K.center a.1)
    (hleaveRight : ∀ b : ↥K.right,
      (leaveGraph P).Adj K.center b.1)
    (hdegreeLeft : ∀ a : ↥K.left,
      (coveredGraph P).degree K.center + (coveredGraph P).degree a.1 ≤
        degreeCutoff)
    (hdegreeRight : ∀ b : ↥K.right,
      (coveredGraph P).degree K.center + (coveredGraph P).degree b.1 ≤
        degreeCutoff)
    (hrootLeft : ∀ a : ↥K.left,
      (rootedActiveForbiddenConfigurations F
        (P ∪ bipartiteLinkReservoir K R) K.center a.1).card ≤
          rootCutoff)
    (hrootRight : ∀ b : ↥K.right,
      (rootedActiveForbiddenConfigurations F
        (P ∪ bipartiteLinkReservoir K R) K.center b.1).card ≤
          rootCutoff)
    (hscalar : degreeCutoff + rootCutoff * familyCutoff ≤ Delta) :
    (∀ a, (deletedNeighbors (bipartiteLinkBadPair F P K R) a).card ≤
      Delta) ∧
    (∀ b, (deletedNeighbors
      (transposeRelation (bipartiteLinkBadPair F P K R)) b).card ≤
        Delta) := by
  constructor
  · intro a
    have h := card_deletedNeighbors_linkDeleted_le F P K R a
      (hleaveLeft a) familyCutoff hfamily
    have hcut :
        (coveredGraph P).degree K.center + (coveredGraph P).degree a.1 +
            (rootedActiveForbiddenConfigurations F
              (P ∪ bipartiteLinkReservoir K R) K.center a.1).card *
              familyCutoff ≤ Delta := by
      exact (Nat.add_le_add (hdegreeLeft a)
        (Nat.mul_le_mul_right familyCutoff (hrootLeft a))).trans hscalar
    change (deletedNeighbors (linkDeleted F P K R) a).card ≤ Delta
    exact h.trans (by
      simpa [bipartiteLinkReservoir] using hcut)
  · intro b
    have h := card_deletedNeighbors_transpose_linkDeleted_le F P K R b
      (hleaveRight b) familyCutoff hfamily
    have hcut :
        (coveredGraph P).degree K.center + (coveredGraph P).degree b.1 +
            (rootedActiveForbiddenConfigurations F
              (P ∪ bipartiteLinkReservoir K R) K.center b.1).card *
              familyCutoff ≤ Delta := by
      exact (Nat.add_le_add (hdegreeRight b)
        (Nat.mul_le_mul_right familyCutoff (hrootRight b))).trans hscalar
    change (deletedNeighbors
      (transposeRelation (linkDeleted F P K R)) b).card ≤ Delta
    exact h.trans (by
      simpa [bipartiteLinkReservoir] using hcut)

/-- Candidate-filtered deletion degrees charge pair conflicts only to the
triangles added after `Pbase`.  This is the form used in the cover-down
iteration: the current available family is legal relative to the historical
packing, while the preliminary, internal, and earlier link choices of the
current stage are precisely the new family `P \ Pbase`. -/
theorem bipartiteLinkRelevantBadDegree_of_cutoffs
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Pbase P : TripleSystemOn V)
    (K : BipartiteLink V)
    (r : ↥K.left → ↥K.right → Prop) [DecidableRel r]
    (R : Finset (↥K.left × ↥K.right))
    (Delta degreeCutoff rootCutoff familyCutoff : ℕ)
    (hfamily : ∀ C ∈ F, C.card ≤ familyCutoff)
    (hbaseSafe : ∀ a b, r a b →
      TriangleAvoidsGraph (coveredGraph Pbase)
        (linkMatchingTriple K.center K.leftEmbedding K.rightEmbedding
          K.center_ne_left K.center_ne_right K.left_ne_right a b))
    (hleaveLeft : ∀ a : ↥K.left,
      (leaveGraph P).Adj K.center a.1)
    (hleaveRight : ∀ b : ↥K.right,
      (leaveGraph P).Adj K.center b.1)
    (hdegreeLeft : ∀ a : ↥K.left,
      (coveredGraph (P \ Pbase)).degree a.1 ≤ degreeCutoff)
    (hdegreeRight : ∀ b : ↥K.right,
      (coveredGraph (P \ Pbase)).degree b.1 ≤ degreeCutoff)
    (hrootLeft : ∀ a : ↥K.left,
      (rootedActiveForbiddenConfigurations F
        (P ∪ bipartiteLinkReservoir K R) K.center a.1).card ≤
          rootCutoff)
    (hrootRight : ∀ b : ↥K.right,
      (rootedActiveForbiddenConfigurations F
        (P ∪ bipartiteLinkReservoir K R) K.center b.1).card ≤
          rootCutoff)
    (hscalar : degreeCutoff + rootCutoff * familyCutoff ≤ Delta) :
    (∀ a, (deletedNeighbors
      (bipartiteLinkRelevantBadPair r F P R) a).card ≤ Delta) ∧
    (∀ b, (deletedNeighbors (transposeRelation
      (bipartiteLinkRelevantBadPair r F P R)) b).card ≤ Delta) := by
  classical
  have hleaveDiffLeft : ∀ a : ↥K.left,
      (leaveGraph (P \ Pbase)).Adj K.center a.1 := by
    intro a
    have hleft := hleaveLeft a
    rw [leaveGraph_adj] at hleft ⊢
    refine ⟨hleft.1, ?_⟩
    rintro ⟨T, hTdiff, hcT, haT, hne⟩
    exact hleft.2
      ⟨T, (mem_sdiff.mp hTdiff).1, hcT, haT, hne⟩
  have hleaveDiffRight : ∀ b : ↥K.right,
      (leaveGraph (P \ Pbase)).Adj K.center b.1 := by
    intro b
    have hright := hleaveRight b
    rw [leaveGraph_adj] at hright ⊢
    refine ⟨hright.1, ?_⟩
    rintro ⟨T, hTdiff, hcT, hbT, hne⟩
    exact hright.2
      ⟨T, (mem_sdiff.mp hTdiff).1, hcT, hbT, hne⟩
  constructor
  · intro a
    have hpair :
        (bipartiteLinkRelevantPairConflictNeighbors r P a).card ≤
          (coveredGraph (P \ Pbase)).degree a.1 := by
      let e : ↥K.right ↪ V := K.rightEmbedding
      have hsub :
          (bipartiteLinkRelevantPairConflictNeighbors r P a).map e ⊆
            (coveredGraph (P \ Pbase)).neighborFinset a.1 := by
        intro v hv
        obtain ⟨b, hb, rfl⟩ := mem_map.mp hv
        rw [SimpleGraph.mem_neighborFinset]
        have hbconf :=
          bipartiteLinkRelevantPairConflictNeighbors_subset_sdiff
            r Pbase P hbaseSafe a hb
        have hnot := (mem_filter.mp hbconf).2
        have hnot' : ¬TriangleAvoidsGraph (coveredGraph (P \ Pbase))
            (thirdVertexTriple (K.center_ne_left a)
              (linkRightThirdVertex K a b)) := by
          rw [thirdVertexTriple_linkRightThirdVertex]
          exact hnot
        have hparts : ¬(
            ¬(coveredGraph (P \ Pbase)).Adj K.center a.1 ∧
            ¬(coveredGraph (P \ Pbase)).Adj K.center b.1 ∧
            ¬(coveredGraph (P \ Pbase)).Adj a.1 b.1) := by
          intro hparts
          exact hnot'
            ((triangleAvoidsGraph_thirdVertexTriple_iff
              (coveredGraph (P \ Pbase)) (K.center_ne_left a)
              (linkRightThirdVertex K a b)).2 hparts)
        have hca : ¬(coveredGraph (P \ Pbase)).Adj K.center a.1 := by
          intro hadj
          exact (leaveGraph_adj.mp (hleaveDiffLeft a)).2
            (coveredGraph_adj.mp hadj)
        have hcb : ¬(coveredGraph (P \ Pbase)).Adj K.center b.1 := by
          intro hadj
          exact (leaveGraph_adj.mp (hleaveDiffRight b)).2
            (coveredGraph_adj.mp hadj)
        tauto
      calc
        (bipartiteLinkRelevantPairConflictNeighbors r P a).card =
            ((bipartiteLinkRelevantPairConflictNeighbors r P a).map e).card :=
          by simp
        _ ≤ ((coveredGraph (P \ Pbase)).neighborFinset a.1).card :=
          card_le_card hsub
        _ = (coveredGraph (P \ Pbase)).degree a.1 := rfl
    have hforbidden :
        (linkForbiddenParticipantNeighbors F P K R a).card ≤
          (rootedActiveForbiddenConfigurations F
            (P ∪ bipartiteLinkReservoir K R) K.center a.1).card *
              familyCutoff := by
      calc
        (linkForbiddenParticipantNeighbors F P K R a).card ≤
            (forbiddenBlockedThirdVertices F (univ : TripleSystemOn V)
              (P ∪ bipartiteLinkReservoir K R)
              (K.center_ne_left a)).card := by
          change (linkForbiddenParticipantNeighbors F P K R a).card ≤
            (forbiddenBlockedThirdVertices F (univ : TripleSystemOn V)
              (P ∪ linkReservoirTriangles K.center K.leftEmbedding
                K.rightEmbedding K.center_ne_left K.center_ne_right
                K.left_ne_right R) (K.center_ne_left a)).card
          exact card_linkForbiddenParticipantNeighbors_le_forbiddenBlocked
            F P K R a
        _ ≤ (rootedActiveForbiddenConfigurations F
              (P ∪ bipartiteLinkReservoir K R) K.center a.1).card *
                familyCutoff :=
          card_forbiddenBlockedThirdVertices_le_mul_rooted_active
            (A := (univ : TripleSystemOn V))
            (P := P ∪ bipartiteLinkReservoir K R)
            (K.center_ne_left a) hfamily
    calc
      (deletedNeighbors
          (bipartiteLinkRelevantBadPair r F P R) a).card ≤
          (bipartiteLinkRelevantPairConflictNeighbors r P a ∪
            linkForbiddenParticipantNeighbors F P K R a).card :=
        card_le_card
          (deletedNeighbors_bipartiteLinkRelevantBadPair_subset
            r F P R a)
      _ ≤ (bipartiteLinkRelevantPairConflictNeighbors r P a).card +
          (linkForbiddenParticipantNeighbors F P K R a).card :=
        card_union_le _ _
      _ ≤ degreeCutoff + rootCutoff * familyCutoff :=
        Nat.add_le_add (hpair.trans (hdegreeLeft a))
          (hforbidden.trans
            (Nat.mul_le_mul_right familyCutoff (hrootLeft a)))
      _ ≤ Delta := hscalar
  · intro b
    have hpair :
        (bipartiteLinkRelevantRightPairConflictNeighbors r P b).card ≤
          (coveredGraph (P \ Pbase)).degree b.1 := by
      let e : ↥K.left ↪ V := K.leftEmbedding
      have hsub :
          (bipartiteLinkRelevantRightPairConflictNeighbors r P b).map e ⊆
            (coveredGraph (P \ Pbase)).neighborFinset b.1 := by
        intro v hv
        obtain ⟨a, ha, rfl⟩ := mem_map.mp hv
        rw [SimpleGraph.mem_neighborFinset]
        have haconf :=
          bipartiteLinkRelevantRightPairConflictNeighbors_subset_sdiff
            r Pbase P hbaseSafe b ha
        have hnot := (mem_filter.mp haconf).2
        have hnot' : ¬TriangleAvoidsGraph (coveredGraph (P \ Pbase))
            (thirdVertexTriple (K.center_ne_right b)
              (linkLeftThirdVertex K b a)) := by
          rw [thirdVertexTriple_linkLeftThirdVertex]
          exact hnot
        have hparts : ¬(
            ¬(coveredGraph (P \ Pbase)).Adj K.center b.1 ∧
            ¬(coveredGraph (P \ Pbase)).Adj K.center a.1 ∧
            ¬(coveredGraph (P \ Pbase)).Adj b.1 a.1) := by
          intro hparts
          exact hnot'
            ((triangleAvoidsGraph_thirdVertexTriple_iff
              (coveredGraph (P \ Pbase)) (K.center_ne_right b)
              (linkLeftThirdVertex K b a)).2 hparts)
        have hcb : ¬(coveredGraph (P \ Pbase)).Adj K.center b.1 := by
          intro hadj
          exact (leaveGraph_adj.mp (hleaveDiffRight b)).2
            (coveredGraph_adj.mp hadj)
        have hca : ¬(coveredGraph (P \ Pbase)).Adj K.center a.1 := by
          intro hadj
          exact (leaveGraph_adj.mp (hleaveDiffLeft a)).2
            (coveredGraph_adj.mp hadj)
        have hba : (coveredGraph (P \ Pbase)).Adj b.1 a.1 := by
          tauto
        exact hba
      calc
        (bipartiteLinkRelevantRightPairConflictNeighbors r P b).card =
            ((bipartiteLinkRelevantRightPairConflictNeighbors r P b).map e).card :=
          by simp
        _ ≤ ((coveredGraph (P \ Pbase)).neighborFinset b.1).card :=
          card_le_card hsub
        _ = (coveredGraph (P \ Pbase)).degree b.1 := rfl
    have hforbidden :
        (linkRightForbiddenParticipantNeighbors F P K R b).card ≤
          (rootedActiveForbiddenConfigurations F
            (P ∪ bipartiteLinkReservoir K R) K.center b.1).card *
              familyCutoff := by
      calc
        (linkRightForbiddenParticipantNeighbors F P K R b).card ≤
            (forbiddenBlockedThirdVertices F (univ : TripleSystemOn V)
              (P ∪ bipartiteLinkReservoir K R)
              (K.center_ne_right b)).card := by
          change (linkRightForbiddenParticipantNeighbors F P K R b).card ≤
            (forbiddenBlockedThirdVertices F (univ : TripleSystemOn V)
              (P ∪ linkReservoirTriangles K.center K.leftEmbedding
                K.rightEmbedding K.center_ne_left K.center_ne_right
                K.left_ne_right R) (K.center_ne_right b)).card
          exact
            card_linkRightForbiddenParticipantNeighbors_le_forbiddenBlocked
              F P K R b
        _ ≤ (rootedActiveForbiddenConfigurations F
              (P ∪ bipartiteLinkReservoir K R) K.center b.1).card *
                familyCutoff :=
          card_forbiddenBlockedThirdVertices_le_mul_rooted_active
            (A := (univ : TripleSystemOn V))
            (P := P ∪ bipartiteLinkReservoir K R)
            (K.center_ne_right b) hfamily
    calc
      (deletedNeighbors (transposeRelation
          (bipartiteLinkRelevantBadPair r F P R)) b).card ≤
          (bipartiteLinkRelevantRightPairConflictNeighbors r P b ∪
            linkRightForbiddenParticipantNeighbors F P K R b).card :=
        card_le_card
          (deletedNeighbors_transpose_bipartiteLinkRelevantBadPair_subset
            r F P R b)
      _ ≤ (bipartiteLinkRelevantRightPairConflictNeighbors r P b).card +
          (linkRightForbiddenParticipantNeighbors F P K R b).card :=
        card_union_le _ _
      _ ≤ degreeCutoff + rootCutoff * familyCutoff :=
        Nat.add_le_add (hpair.trans (hdegreeRight b))
          (hforbidden.trans
            (Nat.mul_le_mul_right familyCutoff (hrootRight b)))
      _ ≤ Delta := hscalar
/-- Simultaneous robustness and statewise degree bounds for unsafe sampled
pairs produce a complete safe simultaneous crossing-link cover. -/
def IsProcessedSimultaneousLinkFamily
    {O V : Type*} [DecidableEq O] [DecidableEq V]
    (K : O → BipartiteLink V) (S : Finset O)
    (M : TripleSystemOn V) : Prop :=
  ∀ T ∈ M, ∃ x : SimultaneousLinkPair O V K,
    x.1 ∈ S ∧ T = simultaneousLinkPairTriple K x

theorem exists_simultaneousLinkCover_of_robust_samples
    {O V : Type*} [Fintype O] [DecidableEq O]
    [Fintype V] [DecidableEq V]
    (U : Finset V) (center : O ↪ V) (K : O → BipartiteLink V)
    (hcenter : ∀ o, (K o).center = center o)
    (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U)
    (hright : ∀ o, (K o).right ⊆ U)
    (F : ForbiddenFamilyOn V) (available P : TripleSystemOn V)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop)
    [rDecidable : ∀ o, DecidableRel (r o)]
    (Delta : ℕ) (omega : SimultaneousLinkPair O V K → Bool)
    (hrobust : ∀ o, IsTwoSidedRobustMatchingSample (r o) Delta
      (simultaneousLinkSelectedPairs K omega o))
    (hPpacking : IsPackingOn P) (hPavoid : AvoidsForbidden P F)
    (havailable : ∀ o a b, r o a b →
      linkMatchingTriple (K o).center (K o).leftEmbedding
        (K o).rightEmbedding (K o).center_ne_left
        (K o).center_ne_right (K o).left_ne_right a b ∈ available)
    (hbadDegree : ∀ (S : Finset O) (P' : TripleSystemOn V),
      P ⊆ P' →
      P' ⊆ P ∪ (available ∩ simultaneousLinkReservoir U center K
        hcenter hout hleft hright omega) →
      IsPackingOn P' → AvoidsForbidden P' F →
      IsProcessedSimultaneousLinkFamily K S (P' \ P) →
      ∀ o, o ∉ S →
        (∀ a, (deletedNeighbors
          (bipartiteLinkRelevantBadPair (r o) F P'
            (simultaneousLinkSelectedPairs K omega o)) a).card ≤ Delta) ∧
        (∀ b, (deletedNeighbors (transposeRelation
          (bipartiteLinkRelevantBadPair (r o) F P'
            (simultaneousLinkSelectedPairs K omega o))) b).card ≤ Delta)) :
    ∃ M : TripleSystemOn V,
      M ⊆ simultaneousLinkReservoir U center K hcenter hout hleft hright
        omega ∧
      IsSimultaneousLinkCover F available P K M := by
  classical
  let reservoir := simultaneousLinkReservoir U center K hcenter hout
    hleft hright omega
  let stageAvailable := available ∩ reservoir
  have hind : ∀ S : Finset O, ∃ P' : TripleSystemOn V,
      P ⊆ P' ∧ P' ⊆ P ∪ stageAvailable ∧
      IsPackingOn P' ∧ AvoidsForbidden P' F ∧
      IsProcessedSimultaneousLinkFamily K S (P' \ P) ∧
      ∀ o ∈ S, CoversBipartiteLink (K o) (P' \ P) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        refine ⟨P, Subset.rfl, subset_union_left, hPpacking, hPavoid,
          ?_, ?_⟩
        · intro T hT
          simp at hT
        · simp
    | @insert o S ho ih =>
        obtain ⟨P', hPP', hP'sub, hP'packing, hP'avoid,
          hprocessed, hcovered⟩ := ih
        have hdegrees := hbadDegree S P' hPP'
          (by simpa only [stageAvailable, reservoir] using hP'sub)
          hP'packing hP'avoid hprocessed o ho
        obtain ⟨M, hMstage, hMlocal, hP'Mdisjoint, hP'Mpacking,
            hP'Mavoid, hMcover⟩ :=
          exists_reservoirLinkCover_of_twoSidedRobustSample
            F stageAvailable P' (K o) (r o) Delta
              (simultaneousLinkSelectedPairs K omega o)
              (hrobust o) hP'packing hP'avoid
              (by
                intro a b hr hab
                apply mem_inter.mpr
                refine ⟨havailable o a b hr, ?_⟩
                exact bipartiteLinkReservoir_simultaneous_subset
                  U center K hcenter hout hleft hright omega o
                  (mem_image.mpr ⟨(a, b), hab, rfl⟩))
              hdegrees.1 hdegrees.2
        let Pnext := P' ∪ M
        have hPPnext : P ⊆ Pnext := hPP'.trans subset_union_left
        have hPnextSub : Pnext ⊆ P ∪ stageAvailable := by
          intro T hT
          rcases mem_union.mp hT with hTP' | hTM
          · exact hP'sub hTP'
          · exact mem_union_right P (hMstage hTM)
        have hMdiff : M ⊆ Pnext \ P := by
          intro T hTM
          apply mem_sdiff.mpr
          refine ⟨mem_union_right P' hTM, ?_⟩
          intro hTP
          exact Finset.disjoint_left.mp hP'Mdisjoint (hPP' hTP) hTM
        have hOldDiff : P' \ P ⊆ Pnext \ P := by
          intro T hT
          exact mem_sdiff.mpr
            ⟨mem_union_left M (mem_sdiff.mp hT).1, (mem_sdiff.mp hT).2⟩
        have hprocessedNext :
            IsProcessedSimultaneousLinkFamily K (insert o S)
              (Pnext \ P) := by
          intro T hT
          have hTPnext := (mem_sdiff.mp hT).1
          rcases mem_union.mp hTPnext with hTP' | hTM
          · obtain ⟨x, hxS, hxT⟩ := hprocessed T
                (mem_sdiff.mpr ⟨hTP', (mem_sdiff.mp hT).2⟩)
            exact ⟨x, mem_insert_of_mem hxS, hxT⟩
          · obtain ⟨ab, hab, hTab⟩ := mem_image.mp (hMlocal hTM)
            refine ⟨⟨o, ab⟩, mem_insert_self o S, ?_⟩
            simpa only [bipartiteLinkReservoir,
              simultaneousLinkPairTriple] using hTab.symm
        refine ⟨Pnext, hPPnext, hPnextSub, hP'Mpacking, hP'Mavoid,
          hprocessedNext, ?_⟩
        intro j hj
        rcases mem_insert.mp hj with rfl | hjS
        · exact hMcover.mono hMdiff
        · exact (hcovered j hjS).mono hOldDiff
  obtain ⟨Pfinal, hPPfinal, hPfinalSub, hPfinalPacking,
      hPfinalAvoid, _hprocessed, hcover⟩ :=
    hind (univ : Finset O)
  let M := Pfinal \ P
  have hMstage : M ⊆ stageAvailable := by
    intro T hTM
    rcases mem_union.mp (hPfinalSub (mem_sdiff.mp hTM).1) with hTP | hTA
    · exact ((mem_sdiff.mp hTM).2 hTP).elim
    · exact hTA
  have hPM : P ∪ M = Pfinal := union_sdiff_of_subset hPPfinal
  have hdisjoint : Disjoint P M := by
    rw [Finset.disjoint_left]
    intro T hTP hTM
    exact (mem_sdiff.mp hTM).2 hTP
  refine ⟨M, ?_, ?_, hdisjoint, ?_, ?_, ?_⟩
  · intro T hTM
    exact (mem_inter.mp (hMstage hTM)).2
  · intro T hTM
    exact (mem_inter.mp (hMstage hTM)).1
  · simpa only [hPM] using hPfinalPacking
  · simpa only [hPM] using hPfinalAvoid
  · intro o
    exact hcover o (mem_univ o)

end

end Erdos207
