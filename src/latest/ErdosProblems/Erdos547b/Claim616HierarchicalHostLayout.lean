/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616HierarchicalHostPools
import ErdosProblems.Erdos547b.Claim616HierarchicalSourceLayout

/-!
# Canonical Claim 6.16 host slots

This module interprets the tagged source slots of the hierarchical allocator
as literal host reservoirs.  Distinguished slots are the exact quantitative
reservoirs retained by `IndexedHostSystem`; selected-cluster and matching-side
slots are their whole clusters with both distinguished reservoirs deleted.
The definitions apply to literal edges of the original Claim-6.7 matching, so
all residual submatchings share one physical collision namespace.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim616HierarchicalHostLayout

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim616HierarchicalHostPools
open Erdos547b.ZhaoClaim616HierarchicalSourceLayout

universe u v

variable {B : Type u} {I : Type v}
variable [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
variable (G : SimpleGraph B) [DecidableRel G.Adj]
variable (cluster : I → Finset B) (epsilon density : ℚ)
variable [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
variable {L O : Finset I} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
variable {C67 : Claim67Certificate
  (regularityReducedGraph G cluster epsilon density) L miss}
variable {degreeA : Finset (MatchingEdge C67.M) → ℝ}
variable
  (D : MatchingDecomposition L O miss C67 lowerV1 upperV1 upperV2 mbBound
    degreeA)
variable (A Broot : I) (C : Finset I) (rhoK : ℕ)
variable (Pcluster : ClusterAssignment B I) (threshold quota : ℕ)
variable (Gdegree : SimpleGraph B) [DecidableRel Gdegree.Adj]
variable
  (H : IndexedHostSystem G cluster epsilon density A Broot C D.Mout
    (D.V2 ∩ (matchingSupport D.Mout \ matchingSupport D.Mb)) rhoK
    Pcluster threshold quota Gdegree)

abbrev RootSlot := Claim616RootSlot C67 C
abbrev Pool := Claim616Pool C67 C

/-- A literal original-matching endpoint after deleting the two distinguished
root reservoirs. -/
def matchingRaw (e : MatchingEdge C67.M) (side : Fin 2) : Finset B :=
  H.removeRootReserves (cluster (matchingEdgeEndpoint e.1 side))

/-- Whole pair-side represented by a tagged root slot. -/
def slotWhole : RootSlot C67 C → Finset B
  | Sum.inl side => if side = 0 then cluster A else cluster Broot
  | Sum.inr (Sum.inl i) => indexedCluster cluster C i
  | Sum.inr (Sum.inr (e, side)) =>
      cluster (matchingEdgeEndpoint e.1 side)

/-- Actual raw reservoir represented by a tagged root slot. -/
def slotRaw : RootSlot C67 C → Finset B
  | Sum.inl side => if side = 0 then H.rootReserve else H.companionReserve
  | Sum.inr (Sum.inl i) => H.selectedRaw i
  | Sum.inr (Sum.inr (e, side)) => matchingRaw G cluster epsilon density D
      A Broot C rhoK Pcluster threshold quota Gdegree H e side

/-- Slots which can occur in the Claim-6.16 source layout.  Residual `M_1`
edges lie in `minEdges`; both `M_out` and `M_b` lie in its complement. -/
def RelevantSlot : RootSlot C67 C → Prop
  | Sum.inl _ => True
  | Sum.inr (Sum.inl _) => True
  | Sum.inr (Sum.inr (e, _)) =>
      e ∈ D.MoneEdges C ∨ e ∈ allMatchingEdges C67.M \ D.minEdges

theorem matchingRaw_subset (e : MatchingEdge C67.M) (side : Fin 2) :
    matchingRaw G cluster epsilon density D A Broot C rhoK Pcluster threshold
        quota Gdegree H e side ⊆ cluster (matchingEdgeEndpoint e.1 side) :=
  H.removeRootReserves_subset _

theorem slotRaw_subset (slot : RootSlot C67 C) :
    slotRaw G cluster epsilon density D A Broot C rhoK Pcluster threshold quota
        Gdegree H slot ⊆
      slotWhole G cluster A Broot C slot := by
  rcases slot with side | i_or_edge
  · fin_cases side
    · simpa [slotRaw, slotWhole] using H.rootReserve_subset
    · simpa [slotRaw, slotWhole] using H.companionReserve_subset
  · rcases i_or_edge with i | edge
    · simpa [slotRaw, slotWhole] using H.selectedRaw_subset i
    · rcases edge with ⟨e, side⟩
      simpa [slotRaw, slotWhole] using matchingRaw_subset G cluster epsilon
        density D A Broot C rhoK Pcluster threshold quota Gdegree H e side

/-- A selected cluster is disjoint from every matching-side slot which can
actually be used by `M_1`, `M_out`, or `M_b`. -/
theorem selectedRaw_disjoint_matchingRaw_of_relevant
    (hCV1 : C ⊆ D.V1) (i : Fin C.card) (e : MatchingEdge C67.M)
    (side : Fin 2)
    (he : e ∈ D.MoneEdges C ∨ e ∈ allMatchingEdges C67.M \ D.minEdges) :
    Disjoint (H.selectedRaw i)
      (matchingRaw G cluster epsilon density D A Broot C rhoK Pcluster
        threshold quota Gdegree H e side) := by
  have hx0 : finsetValue C i ∈ matchingSupport (D.Mzero C) :=
    D.C_subset_Mzero_support C hCV1 (finsetValue_mem C i)
  have hy : matchingEdgeEndpoint e.1 side ∈
      if e ∈ D.MoneEdges C then matchingSupport (D.Mone C)
      else matchingSupport D.Mout := by
    by_cases he1 : e ∈ D.MoneEdges C
    · simp only [he1, if_true]
      exact matchingEdgeEndpoint_mem_edgeFinsetSubgraph_support C67.M L
        (D.MoneEdges C) e he1 side
    · simp only [he1, if_false]
      have heout := he.resolve_left he1
      exact matchingEdgeEndpoint_mem_edgeFinsetSubgraph_support C67.M L
        (allMatchingEdges C67.M \ D.minEdges) e heout side
  have hne : finsetValue C i ≠ matchingEdgeEndpoint e.1 side := by
    intro h
    by_cases he1 : e ∈ D.MoneEdges C
    · apply Finset.disjoint_left.mp (D.Mzero_Mone_support_disjoint C) hx0
      simpa only [he1, if_true, h] using hy
    · apply Finset.disjoint_left.mp (D.Mzero_Mout_support_disjoint C) hx0
      simpa only [he1, if_false, h] using hy
  exact (H.cluster_disjoint _ _ hne).mono H.selectedRaw_subset
    (matchingRaw_subset G cluster epsilon density D A Broot C rhoK Pcluster
      threshold quota Gdegree H e side)

/-- Coordinate-free separation theorem for all relevant tagged slots.  The
hypothesis compares physical pools, so the two orientations of one matching
edge are intentionally allowed to overlap in the online accounting. -/
theorem slotRaw_disjoint_of_relevant_of_pool_ne
    (hCV1 : C ⊆ D.V1) (x y : RootSlot C67 C)
    (hx : RelevantSlot D C x) (hy : RelevantSlot D C y)
    (hpool : ZhaoClaim616HierarchicalSourceLayout.rootSlotPool x ≠
      ZhaoClaim616HierarchicalSourceLayout.rootSlotPool y) :
    Disjoint
      (slotRaw G cluster epsilon density D A Broot C rhoK Pcluster threshold
        quota Gdegree H x)
      (slotRaw G cluster epsilon density D A Broot C rhoK Pcluster threshold
        quota Gdegree H y) := by
  rcases x with sx | cx
  · rcases y with sy | cy
    · fin_cases sx <;> fin_cases sy
      · exact False.elim (hpool rfl)
      · simpa [slotRaw] using rootReserve_disjoint_companionReserve
          G cluster epsilon density D A Broot C rhoK Pcluster threshold quota
            Gdegree H
      · simpa [slotRaw] using (rootReserve_disjoint_companionReserve
          G cluster epsilon density D A Broot C rhoK Pcluster threshold quota
            Gdegree H).symm
      · exact False.elim (hpool rfl)
    · rcases cy with i | edge
      · fin_cases sx
        · simpa [slotRaw] using rootReserve_disjoint_selectedRaw
            G cluster epsilon density D A Broot C rhoK Pcluster threshold quota
              Gdegree H i
        · simpa [slotRaw] using companionReserve_disjoint_selectedRaw
            G cluster epsilon density D A Broot C rhoK Pcluster threshold quota
              Gdegree H i
      · rcases edge with ⟨e, side⟩
        fin_cases sx
        · exact H.rootReserve_disjoint_removed _
        · exact H.companionReserve_disjoint_removed _
  · rcases y with sy | cy
    · exact (slotRaw_disjoint_of_relevant_of_pool_ne G cluster epsilon density
        D A Broot C rhoK Pcluster threshold quota Gdegree H hCV1
        (Sum.inl sy) (Sum.inr cx) hy hx (Ne.symm hpool)).symm
    · rcases cx with i | edgeX
      · rcases cy with j | edgeY
        · have hij : i ≠ j := by
            intro hij
            subst j
            exact hpool rfl
          simpa [slotRaw] using selectedRaw_disjoint_selectedRaw_of_ne
            G cluster epsilon density D A Broot C rhoK Pcluster threshold quota
              Gdegree H i j hij
        · rcases edgeY with ⟨e, side⟩
          exact selectedRaw_disjoint_matchingRaw_of_relevant G cluster epsilon
            density D A Broot C rhoK Pcluster threshold quota Gdegree H hCV1
            i e side hy
      · rcases edgeX with ⟨e, side⟩
        rcases cy with j | edgeY
        · exact (selectedRaw_disjoint_matchingRaw_of_relevant G cluster
            epsilon density D A Broot C rhoK Pcluster threshold quota Gdegree H
            hCV1 j e side hx).symm
        · rcases edgeY with ⟨f, other⟩
          have hef : e ≠ f := by
            intro hef
            subst f
            exact hpool rfl
          have hends := matchingEdgeEndpoint_original_injective C67.M
            C67.isMatching
          have hne : matchingEdgeEndpoint e.1 side ≠
              matchingEdgeEndpoint f.1 other := by
            intro h
            exact hef (congrArg Prod.fst (hends h))
          exact (H.cluster_disjoint _ _ hne).mono
            (matchingRaw_subset G cluster epsilon density D A Broot C rhoK
              Pcluster threshold quota Gdegree H e side)
            (matchingRaw_subset G cluster epsilon density D A Broot C rhoK
              Pcluster threshold quota Gdegree H f other)

/-- Any actual reduced edge supplies its defining whole uniform pair. -/
theorem pair_of_reducedAdj {x y : I}
    (hxy : (regularityReducedGraph G cluster epsilon density).Adj x y) :
    G.IsUniform epsilon (cluster x) (cluster y) ∧
      density ≤ G.edgeDensity (cluster x) (cluster y) :=
  ⟨hxy.2.1, hxy.2.2⟩

/-- The exact distinguished-A to selected-C pair stored in the host
certificate. -/
theorem root_selectedPair (i : Fin C.card) :
    G.IsUniform epsilon (cluster A) (indexedCluster cluster C i) ∧
      density ≤ G.edgeDensity (cluster A) (indexedCluster cluster C i) :=
  H.root_pair i

/-- The selected-C to accessible `M_out` endpoint pair in the orientation
used by the source layout (local side one is the endpoint adjacent to C). -/
theorem selected_accessPair
    (i : Fin C.card) (e : Fin D.Mout.edgeSet.toFinite.toFinset.card)
    (he : e ∈ indexedAllowedEdges
      (regularityReducedGraph G cluster epsilon density)
      D.Mout.edgeSet.toFinite.toFinset matchingEdgeEndpoint C
      (D.V2 ∩ (matchingSupport D.Mout \ matchingSupport D.Mb)) i) :
    let access := indexedAccessSide
      (regularityReducedGraph G cluster epsilon density)
      D.Mout.edgeSet.toFinite.toFinset matchingEdgeEndpoint C
      (D.V2 ∩ (matchingSupport D.Mout \ matchingSupport D.Mb)) i e
    G.IsUniform epsilon (indexedCluster cluster C i)
        (cluster (matchingEdgeEndpoint (moutOriginalEdge D e).1
          (orientedSide access 1))) ∧
      density ≤ G.edgeDensity (indexedCluster cluster C i)
        (cluster (matchingEdgeEndpoint (moutOriginalEdge D e).1
          (orientedSide access 1))) := by
  dsimp only
  have h := H.access_pair i e he
  by_cases hs : indexedAccessSide
      (regularityReducedGraph G cluster epsilon density)
      D.Mout.edgeSet.toFinite.toFinset matchingEdgeEndpoint C
      (D.V2 ∩ (matchingSupport D.Mout \ matchingSupport D.Mb)) i e = 0
  · simpa [orientedSide, hs, moutOriginalEdge_val] using h
  · have hsOne : indexedAccessSide
        (regularityReducedGraph G cluster epsilon density)
        D.Mout.edgeSet.toFinite.toFinset matchingEdgeEndpoint C
        (D.V2 ∩ (matchingSupport D.Mout \ matchingSupport D.Mb)) i e = 1 := by
      apply Fin.ext
      have hlt := (indexedAccessSide
        (regularityReducedGraph G cluster epsilon density)
        D.Mout.edgeSet.toFinite.toFinset matchingEdgeEndpoint C
        (D.V2 ∩ (matchingSupport D.Mout \ matchingSupport D.Mb)) i e).isLt
      have hnzero : (indexedAccessSide
          (regularityReducedGraph G cluster epsilon density)
          D.Mout.edgeSet.toFinite.toFinset matchingEdgeEndpoint C
          (D.V2 ∩ (matchingSupport D.Mout \ matchingSupport D.Mb)) i e).val ≠ 0 := by
        intro hz
        apply hs
        apply Fin.ext
        simpa using hz
      omega
    simpa [orientedSide, hs, hsOne, moutOriginalEdge_val] using h

/-- Every literal original matching edge is a genuine whole regular pair.
This is the common pair fact used for `M_out`, `M_1`, and `M_b`. -/
theorem originalMatchingPair (e : MatchingEdge C67.M) :
    G.IsUniform epsilon
        (cluster (matchingEdgeEndpoint e.1 0))
        (cluster (matchingEdgeEndpoint e.1 1)) ∧
      density ≤ G.edgeDensity
        (cluster (matchingEdgeEndpoint e.1 0))
        (cluster (matchingEdgeEndpoint e.1 1)) := by
  have he : (regularityReducedGraph G cluster epsilon density).Adj
      (matchingEdgeEndpoint e.1 0) (matchingEdgeEndpoint e.1 1) := by
    simpa [matchingEdgeEndpoint_pair_eq] using
      C67.M.adj_sub (show C67.M.Adj e.1.out.1 e.1.out.2 by
        rw [← Subgraph.mem_edgeSet, e.1.out_eq]
        exact e.2)
  exact ⟨he.2.1, he.2.2⟩

/-- The same genuine regular pair in either endpoint orientation. -/
theorem originalMatchingPair_of_ne (e : MatchingEdge C67.M)
    (sourceSide targetSide : Fin 2) (hne : sourceSide ≠ targetSide) :
    G.IsUniform epsilon
        (cluster (matchingEdgeEndpoint e.1 sourceSide))
        (cluster (matchingEdgeEndpoint e.1 targetSide)) ∧
      density ≤ G.edgeDensity
        (cluster (matchingEdgeEndpoint e.1 sourceSide))
        (cluster (matchingEdgeEndpoint e.1 targetSide)) := by
  have hpair := originalMatchingPair G cluster epsilon density D A Broot C rhoK
    Pcluster threshold quota Gdegree H e
  fin_cases sourceSide <;> fin_cases targetSide
  · exact False.elim (hne rfl)
  · simpa using hpair
  · exact ⟨hpair.1.symm, by simpa [G.edgeDensity_comm] using hpair.2⟩
  · exact False.elim (hne rfl)

end Erdos547b.ZhaoClaim616HierarchicalHostLayout

#print axioms Erdos547b.ZhaoClaim616HierarchicalHostLayout.originalMatchingPair
