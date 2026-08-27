/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SupportedTypicalResidualLinks
import ErdosProblems.Erdos207.ReserveProtectedPreliminaryGeometry

/-!
# Residual-link bounds from a sparse crossing reserve

The preliminary cover deliberately removes almost every crossing edge, so
its total covered degree cannot be treated as a perturbative loss.  The
correct comparison is with the sampled crossing reserve.  Every residual
spoke is either sampled or belongs to the nonsampled residual outer graph of
the protected preliminary process.  The latter set has a separately
conditioned small vertex incidence.

This file records the deterministic set and cardinality part of that
argument.  The probabilistic reserve-degree estimates are added in the
following layer.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Vertices of `U` whose spoke from `center` belongs to a prescribed edge
set. -/
def spokeVerticesIn
    {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset V) (edges : Finset (Sym2 V)) (center : V) : Finset V :=
  U.filter fun x ↦ s(center, x) ∈ edges

@[simp]
lemma mem_spokeVerticesIn_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {U : Finset V} {edges : Finset (Sym2 V)} {center x : V} :
    x ∈ spokeVerticesIn U edges center ↔
      x ∈ U ∧ s(center, x) ∈ edges := by
  simp [spokeVerticesIn]

/-- The nonsampled spoke vertices tracked by the protected preliminary
outer-residual law. -/
def protectedResidualSpokeVertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (sampled : Finset (Sym2 V))
    (P : TripleSystemOn V) (center : V) : Finset V :=
  spokeVerticesIn U
    (preliminaryResidualOuterEdges
      (reserveProtectedOuterGraph G U sampled) U P) center

/-- A residual neighbor after the preliminary and internal families is
either supported by a sampled spoke or is one of the nonsampled residual
spokes tracked at the end of the preliminary process. -/
lemma residualNeighbors_subset_sampled_union_protectedResidual
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {U : Finset V} {sampled : Finset (Sym2 V)}
    {P R : TripleSystemOn V} {center : V}
    (hc : center ∉ U) (hPR : P ⊆ R)
    (hinner : residualNeighbors G R center ⊆ U) :
    residualNeighbors G R center ⊆
      spokeVerticesIn U sampled center ∪
        protectedResidualSpokeVertices G U sampled P center := by
  intro x hx
  have hxU : x ∈ U := hinner hx
  by_cases hsampled : s(center, x) ∈ sampled
  · exact mem_union_left _
      (mem_spokeVerticesIn_iff.mpr ⟨hxU, hsampled⟩)
  · apply mem_union_right
    unfold protectedResidualSpokeVertices
    rw [mem_spokeVerticesIn_iff]
    refine ⟨hxU, ?_⟩
    have hxdata := mem_residualNeighbors_iff.mp hx
    have hcross : s(center, x) ∈ crossingEdges G U := by
      rw [mem_crossingEdges_iff]
      refine ⟨?_, isCrossingEdge_mk_iff.mpr (Or.inr ⟨hxU, hc⟩)⟩
      change G.Adj center x
      exact hxdata.1
    have hnotP : s(center, x) ∉ graphEdges (coveredGraph P) := by
      intro hcovered
      apply hxdata.2
      have hadjP : (coveredGraph P).Adj center x := by
        exact mem_graphEdges_iff.mp hcovered
      obtain ⟨T, hTP, hcT, hxT, hcx⟩ := coveredGraph_adj.mp hadjP
      exact coveredGraph_adj.mpr ⟨T, hPR hTP, hcT, hxT, hcx⟩
    have hresCross : s(center, x) ∈
        preliminaryResidualCrossingEdges G U P \ sampled :=
      mem_sdiff.mpr
        ⟨mem_sdiff.mpr ⟨hcross, hnotP⟩, hsampled⟩
    exact residualCrossing_sdiff_reserve_subset_protectedResidualOuter
      G U sampled P hresCross

/-- The nonsampled residual spoke vertices inject into the corresponding
residual outer-edge star. -/
lemma protectedResidualSpokeVertices_card_le_incidence
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (sampled : Finset (Sym2 V))
    (P : TripleSystemOn V) (center : V) (hc : center ∉ U) :
    (protectedResidualSpokeVertices G U sampled P center).card ≤
      (outerIncidentEdges (reserveProtectedOuterGraph G U sampled) U center ∩
        preliminaryResidualOuterEdges
          (reserveProtectedOuterGraph G U sampled) U P).card := by
  let S := protectedResidualSpokeVertices G U sampled P center
  let E := outerIncidentEdges (reserveProtectedOuterGraph G U sampled) U
      center ∩ preliminaryResidualOuterEdges
        (reserveProtectedOuterGraph G U sampled) U P
  let f : ↑S → ↑E := fun x ↦ ⟨s(center, x.1), by
    have hx := mem_spokeVerticesIn_iff.mp x.2
    have heResidual := hx.2
    refine mem_inter.mpr ⟨?_, heResidual⟩
    rw [mem_outerIncidentEdges_iff]
    exact ⟨(mem_sdiff.mp heResidual).1, by simp⟩⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact Sym2.congr_right.mp (congrArg Subtype.val hxy)
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, S, E] using hcard

/-- Ambient link neighbors in the actual residual set are contained in the
sampled-spoke link neighbors together with the small nonsampled residual
star. -/
lemma ambientLinkNeighborsIn_residual_subset_sampled_union_extra
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {U : Finset V} {sampled : Finset (Sym2 V)}
    {A P R : TripleSystemOn V} {center x : V}
    (hc : center ∉ U) (hPR : P ⊆ R)
    (hinner : residualNeighbors G R center ⊆ U) :
    ambientLinkNeighborsIn center A (residualNeighbors G R center) x ⊆
      ambientLinkNeighborsIn center A
          (spokeVerticesIn U sampled center) x ∪
        protectedResidualSpokeVertices G U sampled P center := by
  intro y hy
  have hydata := mem_ambientLinkNeighborsIn_iff.mp hy
  have hsplit := residualNeighbors_subset_sampled_union_protectedResidual
    (sampled := sampled) hc hPR hinner hydata.1
  rcases mem_union.mp hsplit with hsampled | hextra
  · exact mem_union_left _
      (mem_ambientLinkNeighborsIn_iff.mpr ⟨hsampled, hydata.2⟩)
  · exact mem_union_right _ hextra

/-- The same sparse-reserve decomposition controls common link neighbors. -/
lemma ambientLinkCommonNeighborsIn_residual_subset_sampled_union_extra
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {U : Finset V} {sampled : Finset (Sym2 V)}
    {A P R : TripleSystemOn V} {center x y : V}
    (hc : center ∉ U) (hPR : P ⊆ R)
    (hinner : residualNeighbors G R center ⊆ U) :
    ambientLinkCommonNeighborsIn center A
        (residualNeighbors G R center) x y ⊆
      ambientLinkCommonNeighborsIn center A
          (spokeVerticesIn U sampled center) x y ∪
        protectedResidualSpokeVertices G U sampled P center := by
  intro z hz
  have hzdata := mem_ambientLinkCommonNeighborsIn_iff.mp hz
  have hsplit := residualNeighbors_subset_sampled_union_protectedResidual
    (sampled := sampled) hc hPR hinner hzdata.1
  rcases mem_union.mp hsplit with hsampled | hextra
  · exact mem_union_left _
      (mem_ambientLinkCommonNeighborsIn_iff.mpr
        ⟨hsampled, hzdata.2.1, hzdata.2.2⟩)
  · exact mem_union_right _ hextra

/-- Sampled-spoke degree and a residual-star incidence cap give an upper
degree bound on the actual residual link. -/
lemma ambientLinkNeighborsIn_residual_card_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {U : Finset V} {sampled : Finset (Sym2 V)}
    {A P R : TripleSystemOn V} {center x : V}
    (hc : center ∉ U) (hPR : P ⊆ R)
    (hinner : residualNeighbors G R center ⊆ U)
    {D extra : ℕ}
    (hsampled : (ambientLinkNeighborsIn center A
      (spokeVerticesIn U sampled center) x).card ≤ D)
    (hextra : (protectedResidualSpokeVertices G U sampled P center).card ≤
      extra) :
    (ambientLinkNeighborsIn center A
      (residualNeighbors G R center) x).card ≤ D + extra := by
  calc
    (ambientLinkNeighborsIn center A
        (residualNeighbors G R center) x).card ≤
        (ambientLinkNeighborsIn center A
            (spokeVerticesIn U sampled center) x ∪
          protectedResidualSpokeVertices G U sampled P center).card :=
      card_le_card
        (ambientLinkNeighborsIn_residual_subset_sampled_union_extra
          hc hPR hinner)
    _ ≤ (ambientLinkNeighborsIn center A
          (spokeVerticesIn U sampled center) x).card +
        (protectedResidualSpokeVertices G U sampled P center).card :=
      card_union_le _ _
    _ ≤ D + extra := Nat.add_le_add hsampled hextra

/-- Sampled-spoke codegree and the same residual-star incidence cap give an
upper codegree bound on the actual residual link. -/
lemma ambientLinkCommonNeighborsIn_residual_card_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {U : Finset V} {sampled : Finset (Sym2 V)}
    {A P R : TripleSystemOn V} {center x y : V}
    (hc : center ∉ U) (hPR : P ⊆ R)
    (hinner : residualNeighbors G R center ⊆ U)
    {C extra : ℕ}
    (hsampled : (ambientLinkCommonNeighborsIn center A
      (spokeVerticesIn U sampled center) x y).card ≤ C)
    (hextra : (protectedResidualSpokeVertices G U sampled P center).card ≤
      extra) :
    (ambientLinkCommonNeighborsIn center A
      (residualNeighbors G R center) x y).card ≤ C + extra := by
  calc
    (ambientLinkCommonNeighborsIn center A
        (residualNeighbors G R center) x y).card ≤
        (ambientLinkCommonNeighborsIn center A
            (spokeVerticesIn U sampled center) x y ∪
          protectedResidualSpokeVertices G U sampled P center).card :=
      card_le_card
        (ambientLinkCommonNeighborsIn_residual_subset_sampled_union_extra
          hc hPR hinner)
    _ ≤ (ambientLinkCommonNeighborsIn center A
          (spokeVerticesIn U sampled center) x y).card +
        (protectedResidualSpokeVertices G U sampled P center).card :=
      card_union_le _ _
    _ ≤ C + extra := Nat.add_le_add hsampled hextra

/-- A sampled available link neighbor can fail to be an actual residual
neighbor only when its spoke is used by the post-preliminary internal
family.  The preliminary family itself covers no sampled reserve edge. -/
lemma ambientLinkNeighborsIn_sampled_subset_residual_union_internalCovered
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {U : Finset V} {sampled : Finset (Sym2 V)}
    {A Apre P Q R : TripleSystemOn V} {center x : V}
    (htri : ConsistsOfTriangles G A)
    (hPprotected : P ⊆ reserveProtectedAvailable sampled Apre)
    (hR : R = P ∪ Q) :
    ambientLinkNeighborsIn center A
        (spokeVerticesIn U sampled center) x ⊆
      ambientLinkNeighborsIn center A (residualNeighbors G R center) x ∪
        ((coveredGraph Q).neighborFinset center ∩ U) := by
  intro y hy
  have hydata := mem_ambientLinkNeighborsIn_iff.mp hy
  have hyspoke := mem_spokeVerticesIn_iff.mp hydata.1
  have hcyG := (ambientLinkRelation_graph_adjacencies htri hydata.2).2.1
  by_cases hcoveredQ : (coveredGraph Q).Adj center y
  · apply mem_union_right
    exact mem_inter.mpr
      ⟨by simpa only [SimpleGraph.mem_neighborFinset] using hcoveredQ,
        hyspoke.1⟩
  · apply mem_union_left
    apply mem_ambientLinkNeighborsIn_iff.mpr
    refine ⟨mem_residualNeighbors_iff.mpr ⟨hcyG, ?_⟩, hydata.2⟩
    intro hcoveredR
    obtain ⟨T, hTR, hcT, hyT, hcy⟩ := coveredGraph_adj.mp hcoveredR
    rw [hR] at hTR
    rcases mem_union.mp hTR with hTP | hTQ
    · have hcoveredP : s(center, y) ∈ graphEdges (coveredGraph P) := by
        exact mem_graphEdges_iff.mpr
          (coveredGraph_adj.mpr ⟨T, hTP, hcT, hyT, hcy⟩)
      exact reserve_not_covered_of_subset_reserveProtected hPprotected
        s(center, y) hyspoke.2 hcoveredP
    · exact hcoveredQ
        (coveredGraph_adj.mpr ⟨T, hTQ, hcT, hyT, hcy⟩)

/-- A lower sampled-spoke degree estimate loses only the explicitly bounded
number of spokes used by the internal family. -/
lemma ambientLinkNeighborsIn_residual_card_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {U : Finset V} {sampled : Finset (Sym2 V)}
    {A Apre P Q R : TripleSystemOn V} {center x : V}
    (htri : ConsistsOfTriangles G A)
    (hPprotected : P ⊆ reserveProtectedAvailable sampled Apre)
    (hR : R = P ∪ Q) {m loss : ℕ}
    (hsampled : m + loss ≤
      (ambientLinkNeighborsIn center A
        (spokeVerticesIn U sampled center) x).card)
    (hloss : ((coveredGraph Q).neighborFinset center ∩ U).card ≤ loss) :
    m ≤ (ambientLinkNeighborsIn center A
      (residualNeighbors G R center) x).card := by
  have hcard := card_le_card
    (ambientLinkNeighborsIn_sampled_subset_residual_union_internalCovered
      (U := U) (center := center) (x := x)
      htri hPprotected hR)
  have hunion := card_union_le
    (ambientLinkNeighborsIn center A (residualNeighbors G R center) x)
    ((coveredGraph Q).neighborFinset center ∩ U)
  omega

end

end Erdos207
