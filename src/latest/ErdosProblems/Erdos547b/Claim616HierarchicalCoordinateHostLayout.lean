/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616
import ErdosProblems.Erdos547b.Claim616HierarchicalCoordinateSourceLayout

/-!
# Endpoint-sensitive Claim 6.16 host slots

This module deliberately depends only on the checked `Claim616` certificate,
not on the obsolete coarse HostPools layer.  It defines the exact A₀/B₀
deletion candidates on literal edges of the original Claim-6.7 matching and
proves separation for every slot that can occur in `M_out`, `M_1`, or `M_b`.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim616HierarchicalCoordinateHostLayout

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
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

/-- Delete two concrete rich root reserves from an arbitrary reservoir. -/
def removeRootReserves
    (rootReserve companionReserve X : Finset B) : Finset B :=
  X \ (rootReserve ∪ companionReserve)

/-- Whole host cluster represented by a coordinate slot. -/
def slotWhole :
    ZhaoClaim616HierarchicalSourceLayout.RootSlot
      (Fin C.card) (MatchingEdge C67.M) → Finset B
  | Sum.inl side => if side = 0 then cluster A else cluster Broot
  | Sum.inr (Sum.inl i) => indexedCluster cluster C i
  | Sum.inr (Sum.inr (e, side)) => cluster (matchingEdgeEndpoint e.1 side)

/-- Raw host reservoir represented by a coordinate slot. -/
def slotRaw (rootReserve companionReserve : Finset B) :
    ZhaoClaim616HierarchicalSourceLayout.RootSlot
      (Fin C.card) (MatchingEdge C67.M) → Finset B
  | Sum.inl side => if side = 0 then rootReserve else companionReserve
  | Sum.inr (Sum.inl i) =>
      removeRootReserves rootReserve companionReserve
        (indexedCluster cluster C i)
  | Sum.inr (Sum.inr (e, side)) =>
      removeRootReserves rootReserve companionReserve
        (cluster (matchingEdgeEndpoint e.1 side))

/-- Literal slots that occur in the three Claim-6.16 matching families. -/
def RelevantSlot :
    ZhaoClaim616HierarchicalSourceLayout.RootSlot
      (Fin C.card) (MatchingEdge C67.M) → Prop
  | Sum.inl _ => True
  | Sum.inr (Sum.inl _) => True
  | Sum.inr (Sum.inr (e, _)) =>
      e ∈ Erdos547b.ZhaoClaim616.MatchingDecomposition.MoneEdges D C ∨
        e ∈ allMatchingEdges C67.M \ D.minEdges

theorem removeRootReserves_subset
    (rootReserve companionReserve X : Finset B) :
    removeRootReserves rootReserve companionReserve X ⊆ X :=
  Finset.sdiff_subset

theorem slotRaw_subset
    (slot : ZhaoClaim616HierarchicalSourceLayout.RootSlot
      (Fin C.card) (MatchingEdge C67.M)) :
    slotRaw (G := G) (cluster := cluster) (epsilon := epsilon)
        (density := density) (C := C) (C67 := C67)
        H.rootReserve H.companionReserve slot ⊆
      slotWhole (G := G) (cluster := cluster) (epsilon := epsilon)
        (density := density) (A := A) (Broot := Broot)
        (C := C) (C67 := C67) slot := by
  rcases slot with side | i_or_edge
  · fin_cases side
    · simpa [slotRaw, slotWhole] using H.rootReserve_subset
    · simpa [slotRaw, slotWhole] using H.companionReserve_subset
  · rcases i_or_edge with i | edge
    · simpa [slotRaw, slotWhole] using
        (removeRootReserves_subset H.rootReserve H.companionReserve
          (indexedCluster cluster C i))
    · rcases edge with ⟨e, side⟩
      simpa [slotRaw, slotWhole] using
        (removeRootReserves_subset H.rootReserve H.companionReserve
          (cluster (matchingEdgeEndpoint e.1 side)))

/-- Endpoint occurrences of the original matching are injective. -/
theorem matchingEndpoint_injective :
    Function.Injective (fun ec : MatchingEdge C67.M × Fin 2 ↦
      matchingEdgeEndpoint ec.1.1 ec.2) := by
  rintro ⟨e, c⟩ ⟨f, d⟩ hendpoint
  let flip : Fin 2 → Fin 2 := fun q ↦ if q = 0 then 1 else 0
  have horiented (g : MatchingEdge C67.M) (q : Fin 2) :
      orientedEndpoint C67.M ∅ g (flip q) = matchingEdgeEndpoint g.1 q := by
    fin_cases q <;>
      simp [flip, orientedEndpoint, rawEndpoint, matchingEdgeEndpoint]
  have horientedEq :
      orientedEndpoint C67.M ∅ e (flip c) =
        orientedEndpoint C67.M ∅ f (flip d) := by
    simpa only [horiented] using hendpoint
  have hpair : (e, flip c) = (f, flip d) := by
    apply orientedEndpoint_injective C67.M C67.isMatching (∅ : Finset I)
    exact horientedEq
  have hedge : e = f := congrArg Prod.fst hpair
  subst f
  have hside : c = d := by
    have hflip := congrArg Prod.snd hpair
    fin_cases c <;> fin_cases d <;> simp [flip] at hflip ⊢
  subst d
  rfl

/-- Both endpoints of an edge selected by `edgeFinsetSubgraph` belong to its
literal support. -/
theorem matchingEndpoint_mem_edgeFinsetSupport
    (S : Finset (MatchingEdge C67.M)) (e : MatchingEdge C67.M)
    (he : e ∈ S) (side : Fin 2) :
    matchingEdgeEndpoint e.1 side ∈
      matchingSupport (edgeFinsetSubgraph C67.M L S) := by
  rw [matchingSupport_edgeFinsetSubgraph]
  apply Finset.mem_biUnion.mpr
  refine ⟨e, he, ?_⟩
  fin_cases side <;> by_cases h : e.1.out.1 ∈ L <;>
    simp [orientedEndpoint, rawEndpoint, matchingEdgeEndpoint, h]

theorem rootReserve_disjoint_removed
    (rootReserve companionReserve X : Finset B) :
    Disjoint rootReserve
      (removeRootReserves rootReserve companionReserve X) := by
  rw [Finset.disjoint_left]
  intro z hz hzX
  exact (Finset.mem_sdiff.mp hzX).2 (Finset.mem_union_left _ hz)

theorem companionReserve_disjoint_removed
    (rootReserve companionReserve X : Finset B) :
    Disjoint companionReserve
      (removeRootReserves rootReserve companionReserve X) := by
  rw [Finset.disjoint_left]
  intro z hz hzX
  exact (Finset.mem_sdiff.mp hzX).2 (Finset.mem_union_right _ hz)

/-- A selected C-cluster is distinct from every relevant matching endpoint. -/
theorem selected_disjoint_matching_of_relevant
    (hCV1 : C ⊆ D.V1) (i : Fin C.card) (e : MatchingEdge C67.M)
    (side : Fin 2)
    (he : e ∈ Erdos547b.ZhaoClaim616.MatchingDecomposition.MoneEdges D C ∨
      e ∈ allMatchingEdges C67.M \ D.minEdges) :
    Disjoint
      (removeRootReserves H.rootReserve H.companionReserve
        (indexedCluster cluster C i))
      (removeRootReserves H.rootReserve H.companionReserve
        (cluster (matchingEdgeEndpoint e.1 side))) := by
  have hx0 : finsetValue C i ∈ matchingSupport
      (Erdos547b.ZhaoClaim616.MatchingDecomposition.Mzero D C) :=
    Erdos547b.ZhaoClaim616.MatchingDecomposition.C_subset_Mzero_support
      D C hCV1 (finsetValue_mem C i)
  have hy : matchingEdgeEndpoint e.1 side ∈
      if e ∈ Erdos547b.ZhaoClaim616.MatchingDecomposition.MoneEdges D C then
        matchingSupport
          (Erdos547b.ZhaoClaim616.MatchingDecomposition.Mone D C)
      else matchingSupport D.Mout := by
    by_cases he1 :
        e ∈ Erdos547b.ZhaoClaim616.MatchingDecomposition.MoneEdges D C
    · simp only [he1, if_true]
      exact matchingEndpoint_mem_edgeFinsetSupport (G := G)
        (cluster := cluster) (epsilon := epsilon) (density := density)
        (C67 := C67) (L := L)
        (S := Erdos547b.ZhaoClaim616.MatchingDecomposition.MoneEdges D C)
        (e := e) he1 side
    · simp only [he1, if_false]
      exact matchingEndpoint_mem_edgeFinsetSupport (G := G)
        (cluster := cluster) (epsilon := epsilon) (density := density)
        (C67 := C67) (L := L)
        (S := allMatchingEdges C67.M \ D.minEdges) (e := e)
        (he.resolve_left he1) side
  have hne : finsetValue C i ≠ matchingEdgeEndpoint e.1 side := by
    intro h
    by_cases he1 :
        e ∈ Erdos547b.ZhaoClaim616.MatchingDecomposition.MoneEdges D C
    · apply Finset.disjoint_left.mp
        (Erdos547b.ZhaoClaim616.MatchingDecomposition.Mzero_Mone_support_disjoint
          D C) hx0
      simpa only [he1, if_true, h] using hy
    · apply Finset.disjoint_left.mp
        (Erdos547b.ZhaoClaim616.MatchingDecomposition.Mzero_Mout_support_disjoint
          D C) hx0
      simpa only [he1, if_false, h] using hy
  exact (H.cluster_disjoint _ _ hne).mono
    ((removeRootReserves_subset H.rootReserve H.companionReserve _).trans
      (by simpa [indexedCluster]))
    (removeRootReserves_subset H.rootReserve H.companionReserve _)

/-- Distinct relevant coordinate slots have disjoint raw reservoirs. -/
theorem slotRaw_disjoint_of_relevant_of_ne
    (hCV1 : C ⊆ D.V1)
    (x y : ZhaoClaim616HierarchicalSourceLayout.RootSlot
      (Fin C.card) (MatchingEdge C67.M))
    (hx : RelevantSlot (G := G) (cluster := cluster) (epsilon := epsilon)
      (density := density) (D := D) (C := C) x)
    (hy : RelevantSlot (G := G) (cluster := cluster) (epsilon := epsilon)
      (density := density) (D := D) (C := C) y)
    (hxy : x ≠ y) :
    Disjoint
      (slotRaw (G := G) (cluster := cluster) (epsilon := epsilon)
        (density := density) (C := C) (C67 := C67)
        H.rootReserve H.companionReserve x)
      (slotRaw (G := G) (cluster := cluster) (epsilon := epsilon)
        (density := density) (C := C) (C67 := C67)
        H.rootReserve H.companionReserve y) := by
  rcases x with sx | cx
  · rcases y with sy | cy
    · fin_cases sx <;> fin_cases sy
      · exact False.elim (hxy rfl)
      · simpa [slotRaw] using H.distinguished_cluster_disjoint.mono
          H.rootReserve_subset H.companionReserve_subset
      · simpa [slotRaw] using (H.distinguished_cluster_disjoint.mono
          H.rootReserve_subset H.companionReserve_subset).symm
      · exact False.elim (hxy rfl)
    · rcases cy with i | edge
      · fin_cases sx
        · simpa [slotRaw] using rootReserve_disjoint_removed H.rootReserve
            H.companionReserve
            (indexedCluster cluster C i)
        · simpa [slotRaw] using companionReserve_disjoint_removed
            H.rootReserve H.companionReserve
            (indexedCluster cluster C i)
      · rcases edge with ⟨e, side⟩
        fin_cases sx
        · simpa [slotRaw] using rootReserve_disjoint_removed H.rootReserve
            H.companionReserve
              (cluster (matchingEdgeEndpoint e.1 side))
        · simpa [slotRaw] using companionReserve_disjoint_removed
            H.rootReserve H.companionReserve
              (cluster (matchingEdgeEndpoint e.1 side))
  · rcases y with sy | cy
    · rcases cx with i | edge
      · fin_cases sy
        · simpa [slotRaw] using (rootReserve_disjoint_removed H.rootReserve
            H.companionReserve (indexedCluster cluster C i)).symm
        · simpa [slotRaw] using (companionReserve_disjoint_removed
            H.rootReserve H.companionReserve
            (indexedCluster cluster C i)).symm
      · rcases edge with ⟨e, side⟩
        fin_cases sy
        · simpa [slotRaw] using (rootReserve_disjoint_removed H.rootReserve
            H.companionReserve
            (cluster (matchingEdgeEndpoint e.1 side))).symm
        · simpa [slotRaw] using (companionReserve_disjoint_removed
            H.rootReserve H.companionReserve
            (cluster (matchingEdgeEndpoint e.1 side))).symm
    · rcases cx with i | edgeX
      · rcases cy with j | edgeY
        · have hij : i ≠ j := by
            intro hij
            subst j
            exact hxy rfl
          have hcluster : finsetValue C i ≠ finsetValue C j := by
            intro h
            exact hij (finsetValue_injective C h)
          exact (H.cluster_disjoint _ _ hcluster).mono
            ((removeRootReserves_subset H.rootReserve H.companionReserve _).trans
              (by simpa [indexedCluster]))
            ((removeRootReserves_subset H.rootReserve H.companionReserve _).trans
              (by simpa [indexedCluster]))
        · rcases edgeY with ⟨e, side⟩
          exact selected_disjoint_matching_of_relevant (G := G)
            (cluster := cluster) (epsilon := epsilon) (density := density)
            (D := D) (A := A) (Broot := Broot) (C := C)
            (rhoK := rhoK) (Pcluster := Pcluster) (threshold := threshold)
            (quota := quota) (Gdegree := Gdegree) (H := H) hCV1 i e side hy
      · rcases edgeX with ⟨e, side⟩
        rcases cy with j | edgeY
        · exact (selected_disjoint_matching_of_relevant (G := G)
            (cluster := cluster) (epsilon := epsilon) (density := density)
            (D := D) (A := A) (Broot := Broot) (C := C)
            (rhoK := rhoK) (Pcluster := Pcluster) (threshold := threshold)
            (quota := quota) (Gdegree := Gdegree) (H := H) hCV1 j e side hx).symm
        · rcases edgeY with ⟨f, other⟩
          have hendpoint : matchingEdgeEndpoint e.1 side ≠
              matchingEdgeEndpoint f.1 other := by
            intro h
            exact hxy (congrArg (fun q ↦ Sum.inr (Sum.inr q))
              (matchingEndpoint_injective (G := G) (cluster := cluster)
                (epsilon := epsilon) (density := density) (C67 := C67) h))
          exact (H.cluster_disjoint _ _ hendpoint).mono
            (removeRootReserves_subset H.rootReserve H.companionReserve _)
            (removeRootReserves_subset H.rootReserve H.companionReserve _)

end Erdos547b.ZhaoClaim616HierarchicalCoordinateHostLayout

#print axioms Erdos547b.ZhaoClaim616HierarchicalCoordinateHostLayout.slotRaw_disjoint_of_relevant_of_ne
