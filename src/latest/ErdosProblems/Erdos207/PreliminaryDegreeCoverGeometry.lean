/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourcePreliminaryDegreeTail
import ErdosProblems.Erdos207.SparseReserveResidualLinkBounds

/-! # One preliminary degree event supplies internal scheduling and link recentering -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem PreliminaryResidualDegreeGood.mono_selected
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} {P Q : TripleSystemOn V} {d : ℕ}
    (h : PreliminaryResidualDegreeGood G U P d) (hPQ : P ⊆ Q) :
    PreliminaryResidualDegreeGood G U Q d := by
  intro v
  apply le_trans (card_le_card (show scheduledEdgesAt (graphEdges G) v ∩ preliminaryResidualOuterEdges G U Q ⊆
    scheduledEdgesAt (graphEdges G) v ∩ preliminaryResidualOuterEdges G U P from ?_)) (h v)
  intro e he
  obtain ⟨hstar,houter,hnot⟩ := (mem_inter.mp he).imp_right mem_sdiff.mp
  refine mem_inter.mpr ⟨hstar, mem_sdiff.mpr ⟨houter, ?_⟩⟩
  intro hcovered
  apply hnot
  exact mem_graphEdges_iff.mpr
    ((SimpleGraph.edgeSet_subset_edgeSet.mpr (coveredGraph_mono hPQ)) (mem_graphEdges_iff.mp hcovered))

theorem PreliminaryResidualDegreeGood.internal_incidence
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} {sampled : Finset (Sym2 V)} {P : TripleSystemOn V} {d : ℕ}
    (h : PreliminaryResidualDegreeGood (reserveProtectedOuterGraph G U sampled) U P d)
    (hsampled : sampled ⊆ crossingEdges G U) :
    ∀ v, (scheduledEdgesAt (preliminaryResidualInternalEdges G U P) v).card ≤ d := by
  intro v
  apply le_trans (card_le_card (show scheduledEdgesAt (preliminaryResidualInternalEdges G U P) v ⊆
    scheduledEdgesAt (graphEdges (reserveProtectedOuterGraph G U sampled)) v ∩
      preliminaryResidualOuterEdges (reserveProtectedOuterGraph G U sampled) U P from ?_)) (h v)
  intro e he
  have hh := mem_scheduledEdgesAt_iff.mp he
  have hres := preliminaryResidualInternalEdges_subset_protectedResidualOuter G U sampled P hsampled hh.1
  exact mem_inter.mpr ⟨mem_scheduledEdgesAt_iff.mpr
    ⟨(mem_outerGraphEdges_iff.mp (mem_sdiff.mp hres).1).1,hh.2⟩,hres⟩

theorem PreliminaryResidualDegreeGood.protected_spokes
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} {sampled : Finset (Sym2 V)} {P : TripleSystemOn V} {d : ℕ}
    (h : PreliminaryResidualDegreeGood (reserveProtectedOuterGraph G U sampled) U P d)
    {center : V} (hc : center ∉ U) :
    (protectedResidualSpokeVertices G U sampled P center).card ≤ d := by
  apply (protectedResidualSpokeVertices_card_le_incidence G U sampled P center hc).trans
  apply le_trans (card_le_card (show outerIncidentEdges (reserveProtectedOuterGraph G U sampled) U center ∩
    preliminaryResidualOuterEdges (reserveProtectedOuterGraph G U sampled) U P ⊆
      scheduledEdgesAt (graphEdges (reserveProtectedOuterGraph G U sampled)) center ∩
        preliminaryResidualOuterEdges (reserveProtectedOuterGraph G U sampled) U P from ?_)) (h center)
  intro e he
  have hh := mem_outerIncidentEdges_iff.mp (mem_inter.mp he).1
  exact mem_inter.mpr ⟨mem_scheduledEdgesAt_iff.mpr
    ⟨(mem_outerGraphEdges_iff.mp hh.1).1,Sym2.mem_toFinset.mp hh.2⟩,(mem_inter.mp he).2⟩

theorem PreliminaryResidualDegreeGood.internal_covered_neighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} {sampled : Finset (Sym2 V)} {P Q : TripleSystemOn V} {d : ℕ}
    (h : PreliminaryResidualDegreeGood (reserveProtectedOuterGraph G U sampled) U P d)
    (hsampled : sampled ⊆ crossingEdges G U) (hpacking : IsPackingOn Q)
    (huse : NewTrianglesUseScheduledOuterEdges U (preliminaryResidualInternalEdges G U P) P Q)
    {center : V} (hc : center ∉ U) :
    (((coveredGraph (Q \ P)).neighborFinset center) ∩ U).card ≤ 2 * d := by
  have hstar := card_triplesThrough_sdiff_le_scheduledEdgesAt hpacking
    (fun _ he ↦ (mem_internalOuterEdges_iff.mp
      (preliminaryResidualInternalEdges_subset_internalOuterEdges G U P he)).2) huse hc
  have hdegree := hstar.trans (h.internal_incidence hsampled center)
  calc
    _ ≤ ((coveredGraph (Q \ P)).neighborFinset center).card := card_le_card inter_subset_left
    _ = (coveredGraph (Q \ P)).degree center := SimpleGraph.card_neighborFinset_eq_degree _ _
    _ = 2 * (triplesThrough (Q \ P) center).card :=
      (hpacking.mono sdiff_subset).coveredGraph_degree_eq_two_mul_triplesThrough center
    _ ≤ _ := Nat.mul_le_mul_left _ hdegree

end

end Erdos207
