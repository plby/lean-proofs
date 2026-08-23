/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos551.External.Erdos207.MultiLinkCover
import ErdosProblems.Erdos551.External.Erdos207.CompatibleCandidateDegree

/-!
# Residual crossing links

This file defines the exact link vertex set used in the `M^\ddagger` phase:
the neighbors of an outer center whose graph edges have not yet been covered.
Packing parity makes that set even.  A balanced bipartition therefore exists,
and simultaneous covers of those bipartite links cover every graph edge with
an endpoint outside the next vortex set.
-/

namespace Erdos207

open Finset

noncomputable section

/-- Neighbors of `v` whose `G`-edge has not yet been covered by `P`. -/
def residualNeighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : TripleSystemOn V) (v : V) : Finset V :=
  (G \ coveredGraph P).neighborFinset v

@[simp]
lemma mem_residualNeighbors_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : TripleSystemOn V} {u v : V} :
    u ∈ residualNeighbors G P v ↔
      G.Adj v u ∧ ¬ (coveredGraph P).Adj v u := by
  simp only [residualNeighbors, SimpleGraph.mem_neighborFinset,
    SimpleGraph.sdiff_adj]

lemma center_not_mem_residualNeighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : TripleSystemOn V) (v : V) :
    v ∉ residualNeighbors G P v := by
  simp

private lemma coveredGraph_le_of_consists
    {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {P : TripleSystemOn V}
    (htri : ConsistsOfTriangles G P) : coveredGraph P ≤ G := by
  intro u v huv
  obtain ⟨T, hTP, huT, hvT, huv⟩ := coveredGraph_adj.mp huv
  exact htri T hTP u huT v hvT huv

/-- Removing the pairs of a packing from an even graph leaves even degree at
every vertex. -/
theorem residualNeighbors_even
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : TripleSystemOn V}
    (heven : ∀ v, Even (G.degree v))
    (htri : ConsistsOfTriangles G P) (hpacking : IsPackingOn P)
    (v : V) : Even (residualNeighbors G P v).card := by
  have hcovered : coveredGraph P ≤ G := coveredGraph_le_of_consists htri
  have hneighbors : (coveredGraph P).neighborFinset v ⊆
      G.neighborFinset v := by
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw ⊢
    exact hcovered hw
  have hcard : (residualNeighbors G P v).card =
      G.degree v - (coveredGraph P).degree v := by
    rw [residualNeighbors, SimpleGraph.neighborFinset_sdiff,
      Finset.card_sdiff_of_subset hneighbors,
      SimpleGraph.card_neighborFinset_eq_degree,
      SimpleGraph.card_neighborFinset_eq_degree]
  obtain ⟨a, ha⟩ := heven v
  have hcoveredDegree := hpacking.coveredGraph_degree_eq_two_mul_triplesThrough v
  have hdegreeLe : (coveredGraph P).degree v ≤ G.degree v :=
    SimpleGraph.degree_le_of_le hcovered
  refine ⟨a - (triplesThrough P v).card, ?_⟩
  rw [hcard, hcoveredDegree]
  omega

/-- A canonical balanced bipartition of the residual link.  It is
noncomputable only because no particular half of the finite set is preferred.
-/
def residualBipartiteLink
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : TripleSystemOn V) (v : V)
    (heven : Even (residualNeighbors G P v).card) : BipartiteLink V :=
  Classical.choose (BipartiteLink.exists_balanced_of_even v
    (residualNeighbors G P v)
    (center_not_mem_residualNeighbors G P v) heven)

lemma residualBipartiteLink_center
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : TripleSystemOn V) (v : V)
    (heven : Even (residualNeighbors G P v).card) :
    (residualBipartiteLink G P v heven).center = v :=
  (Classical.choose_spec (BipartiteLink.exists_balanced_of_even v
    (residualNeighbors G P v)
    (center_not_mem_residualNeighbors G P v) heven)).1

lemma residualBipartiteLink_union
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : TripleSystemOn V) (v : V)
    (heven : Even (residualNeighbors G P v).card) :
    (residualBipartiteLink G P v heven).left ∪
      (residualBipartiteLink G P v heven).right =
        residualNeighbors G P v :=
  (Classical.choose_spec (BipartiteLink.exists_balanced_of_even v
    (residualNeighbors G P v)
    (center_not_mem_residualNeighbors G P v) heven)).2.1

lemma residualBipartiteLink_balanced
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : TripleSystemOn V) (v : V)
    (heven : Even (residualNeighbors G P v).card) :
    (residualBipartiteLink G P v heven).left.card =
      (residualBipartiteLink G P v heven).right.card :=
  (Classical.choose_spec (BipartiteLink.exists_balanced_of_even v
    (residualNeighbors G P v)
    (center_not_mem_residualNeighbors G P v) heven)).2.2

/-- Covering the canonical bipartite link covers every residual edge at its
center. -/
theorem CoversBipartiteLink.covers_residualNeighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {P M : TripleSystemOn V} {v : V}
    {heven : Even (residualNeighbors G P v).card}
    (hcover : CoversBipartiteLink
      (residualBipartiteLink G P v heven) M) :
    ∀ w ∈ residualNeighbors G P v, (coveredGraph M).Adj v w := by
  intro w hw
  have hwUnion : w ∈
      (residualBipartiteLink G P v heven).left ∪
        (residualBipartiteLink G P v heven).right := by
    rw [residualBipartiteLink_union G P v heven]
    exact hw
  have hcenter := residualBipartiteLink_center G P v heven
  rcases mem_union.mp hwUnion with hwL | hwR
  · simpa only [hcenter] using hcover.1 w hwL
  · simpa only [hcenter] using hcover.2 w hwR

/-- Once every outer residual link is covered, every old graph edge outside
`U` is covered by the old packing or by the new link family. -/
theorem covers_outside_of_residualLink_covers
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {U : Finset V} {P M : TripleSystemOn V}
    (heven : ∀ v, Even (residualNeighbors G P v).card)
    (hlinks : ∀ v : {x : V // x ∉ U},
      CoversBipartiteLink
        (residualBipartiteLink G P v.1 (heven v.1)) M) :
    ∀ u v : V, G.Adj u v → (u ∉ U ∨ v ∉ U) →
      (coveredGraph (P ∪ M)).Adj u v := by
  intro u v huv hout
  by_cases hP : (coveredGraph P).Adj u v
  · obtain ⟨T, hTP, huT, hvT, huvT⟩ := coveredGraph_adj.mp hP
    exact coveredGraph_adj.mpr
      ⟨T, mem_union_left M hTP, huT, hvT, huvT⟩
  · have liftM : ∀ {x y}, (coveredGraph M).Adj x y →
        (coveredGraph (P ∪ M)).Adj x y := by
      intro x y hxy
      obtain ⟨T, hTM, hxT, hyT, hxyT⟩ := coveredGraph_adj.mp hxy
      exact coveredGraph_adj.mpr
        ⟨T, mem_union_right P hTM, hxT, hyT, hxyT⟩
    rcases hout with hu | hv
    · let o : {x : V // x ∉ U} := ⟨u, hu⟩
      have hvRes : v ∈ residualNeighbors G P u :=
        mem_residualNeighbors_iff.mpr ⟨huv, hP⟩
      exact liftM ((hlinks o).covers_residualNeighbors v hvRes)
    · let o : {x : V // x ∉ U} := ⟨v, hv⟩
      have huRes : u ∈ residualNeighbors G P v :=
        mem_residualNeighbors_iff.mpr ⟨huv.symm, fun h ↦ hP h.symm⟩
      exact liftM (((hlinks o).covers_residualNeighbors u huRes).symm)

/-- Structural endpoint of the full crossing-link phase.  `R0` is the
already chosen stage family whose covered graph edges determine the residual
links, whereas `P0` is the entire old selected family against which packing
and forbidden safety are enforced. -/
theorem exists_crossingLinkCover
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {U : Finset V} {F : ForbiddenFamilyOn V}
    {available P0 R0 : TripleSystemOn V}
    (heven : ∀ v, Even (G.degree v))
    (hRtri : ConsistsOfTriangles G R0) (hRpacking : IsPackingOn R0)
    (hP0packing : IsPackingOn P0) (hP0avoid : AvoidsForbidden P0 F)
    (hstep : ∀ (P : TripleSystemOn V),
      P0 ⊆ P → P ⊆ P0 ∪ available →
      IsPackingOn P → AvoidsForbidden P F →
      ∀ o : {x : V // x ∉ U},
        HasLinkCoverExtension F available P
          (residualBipartiteLink G R0 o.1
            (residualNeighbors_even heven hRtri hRpacking o.1))) :
    ∃ M : TripleSystemOn V,
      M ⊆ available ∧ Disjoint P0 M ∧
      IsPackingOn (P0 ∪ M) ∧ AvoidsForbidden (P0 ∪ M) F ∧
      ∀ u v : V, G.Adj u v → (u ∉ U ∨ v ∉ U) →
        (coveredGraph (R0 ∪ M)).Adj u v := by
  let evenResidual : ∀ v, Even (residualNeighbors G R0 v).card :=
    fun v ↦ residualNeighbors_even heven hRtri hRpacking v
  let K : {x : V // x ∉ U} → BipartiteLink V := fun o ↦
    residualBipartiteLink G R0 o.1 (evenResidual o.1)
  obtain ⟨M, hMavailable, hP0Mdisjoint, hP0Mpacking, hP0Mavoid,
      hlinks⟩ :=
    exists_simultaneous_bipartiteLink_cover F available P0 K
      hP0packing hP0avoid (by
        intro P hP0P hPsub hPpacking hPavoid o
        simpa only [K, evenResidual] using
          hstep P hP0P hPsub hPpacking hPavoid o)
  refine ⟨M, hMavailable, hP0Mdisjoint, hP0Mpacking, hP0Mavoid, ?_⟩
  exact covers_outside_of_residualLink_covers evenResidual (by
    intro o
    simpa only [K, evenResidual] using hlinks o)

end

end Erdos207
