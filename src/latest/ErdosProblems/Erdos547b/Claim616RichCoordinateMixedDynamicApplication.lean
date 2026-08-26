/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616CoordinateMixedDynamicEmbedding
import ErdosProblems.Erdos547b.Claim616RichCoordinateFacts
import ErdosProblems.Erdos547b.Claim616CoordinateCanonicalOptional

/-!
# Rich-host application of the mixed dynamic Claim 6.16 hierarchy

The selected/static coordinate application uses a single capacity for both
endpoints of a matching edge.  This module instead specializes the genuine
dynamic hierarchy constructor.  All pool inclusion, relevance, separation,
matching-pair regularity, and selected-root regularity facts are derived from
the concrete indexed host.  The caller supplies only the six prefix-dependent
residual inequalities in `MixedDynamicResidualFacts`.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim616RichCoordinateMixedDynamicApplication

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim68ParityHalf
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim616HierarchicalAllocation
open Erdos547b.ZhaoClaim616HierarchicalSourceLayout
open Erdos547b.ZhaoClaim616HierarchicalCoordinateSourceLayout
open Erdos547b.ZhaoClaim616HierarchicalCoordinateHostLayout
open Erdos547b.ZhaoClaim616CoordinateEdgeMaps
open Erdos547b.ZhaoClaim616CoordinateHostPairs
open Erdos547b.ZhaoClaim616CoordinateOrientation
open Erdos547b.ZhaoClaim616CoordinateSlotRelevance
open Erdos547b.ZhaoClaim616CoordinateCanonicalOptional
open Erdos547b.ZhaoClaim616RichCoordinateAllocation
open Erdos547b.ZhaoClaim616RichCoordinateFacts
open Erdos547b.ZhaoClaim616CoordinateMixedDynamicLayout
open Erdos547b.ZhaoClaim616CoordinateMixedDynamicEmbedding
open Erdos547b.ZhaoLemma59HierarchicalCoordinateMixedDynamicOnline.HierarchicalSegmentForest

universe u v w

variable {V : Type u} {B : Type v} {K : Type w}
variable [Fintype V] [DecidableEq V]
variable [Fintype B] [DecidableEq B] [Fintype K] [DecidableEq K]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small target slack : ℕ}
variable (G Gdegree : SimpleGraph B)
variable [DecidableRel G.Adj] [DecidableRel Gdegree.Adj]
variable (cluster : K → Finset B) (epsilon density : ℚ)
variable [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
variable {L O : Finset K} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
variable {C67 : Claim67Certificate
  (regularityReducedGraph G cluster epsilon density) L miss}
variable {degreeA : Finset (MatchingEdge C67.M) → ℝ}
variable
  (D : MatchingDecomposition L O miss C67 lowerV1 upperV1 upperV2 mbBound
    degreeA)
variable (Aroot Broot : K) (C : Finset K) (rhoK : ℕ)
variable (Pcluster : ClusterAssignment B K) (threshold quota : ℕ)
variable
  (H : IndexedHostSystem G cluster epsilon density Aroot Broot C
    (MatchingDecomposition.Mout
      (R := regularityReducedGraph G cluster epsilon density) D)
    (MatchingDecomposition.V2
        (R := regularityReducedGraph G cluster epsilon density) D ∩
      (matchingSupport (MatchingDecomposition.Mout
          (R := regularityReducedGraph G cluster epsilon density) D) \
        matchingSupport (MatchingDecomposition.Mb
          (R := regularityReducedGraph G cluster epsilon density) D)))
    rhoK Pcluster threshold quota Gdegree)

abbrev mixedRichAllowed0 (i : Fin C.card) :=
  indexedAllowedEdges (regularityReducedGraph G cluster epsilon density)
    (MatchingDecomposition.Mout
      (R := regularityReducedGraph G cluster epsilon density) D).edgeSet.toFinite.toFinset
    matchingEdgeEndpoint C
    (MatchingDecomposition.V2
        (R := regularityReducedGraph G cluster epsilon density) D ∩
      (matchingSupport (MatchingDecomposition.Mout
          (R := regularityReducedGraph G cluster epsilon density) D) \
        matchingSupport (MatchingDecomposition.Mb
          (R := regularityReducedGraph G cluster epsilon density) D))) i

abbrev mixedRichWhole :=
  slotWhole (G := G) (cluster := cluster) (epsilon := epsilon)
    (density := density) (A := Aroot) (Broot := Broot) (C := C)
    (C67 := C67)

/-- Remove the already chosen image of the original global root from every
dynamic coordinate pool. -/
abbrev mixedRichRawAfterRoot
    (rootReserve companionReserve : Finset B) (z : B)
    (p : RootSlot (Fin C.card) (MatchingEdge C67.M)) : Finset B :=
  slotRaw (G := G) (cluster := cluster) (epsilon := epsilon)
    (density := density) (C := C) (C67 := C67)
    rootReserve companionReserve p \ {z}

private theorem isUniform_real_of_rat
    {X Y : Finset B} (h : G.IsUniform epsilon X Y) :
    G.IsUniform (epsilon : ℝ) X Y := by
  intro X' hX' Y' hY' hXlarge hYlarge
  have hXlargeQ : (#X : ℚ) * epsilon ≤ (#X' : ℚ) := by
    exact_mod_cast hXlarge
  have hYlargeQ : (#Y : ℚ) * epsilon ≤ (#Y' : ℚ) := by
    exact_mod_cast hYlarge
  exact_mod_cast h hX' hY' hXlargeQ hYlargeQ

private theorem matchingEndpoint_zero_ne_one (e : MatchingEdge C67.M) :
    matchingEdgeEndpoint e.1 0 ≠ matchingEdgeEndpoint e.1 1 := by
  intro heq
  have hp : (e, (0 : Fin 2)) = (e, 1) :=
    (matchingEndpoint_injective (G := G) (cluster := cluster)
    (epsilon := epsilon) (density := density) (C67 := C67)
    heq)
  have hs : (0 : Fin 2) = 1 := congrArg Prod.snd hp
  exact Fin.zero_ne_one hs

variable {target slack : ℕ}

/-- Concrete rich-host realization through the genuine mixed dynamic local
steps.  No copy, embedding, or continuation is an input. -/
theorem isContained_of_richMixedDynamicResidualFacts
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb : ℕ)
    (Aalloc : SourceSegmentAllocation hT P (canonicalOptional P) S
      (fun _ : Fin C.card ↦ clusterCap)
      (mixedRichAllowed0 G cluster epsilon density D C)
      (fun _ : RemainingMinEdge
        (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
      (fun _ : ReservedEdge
        (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb) base0)
    (mbSide : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D → Fin 2)
    (hCV1 : C ⊆ MatchingDecomposition.V1
      (R := regularityReducedGraph G cluster epsilon density) D)
    (z : B)
    (R : MixedDynamicResidualFacts
      (AllocationHierarchy hT P (canonicalOptional P)) G
      (fun _ : Fin 1 => z)
      (mixedSourceRootOnly hT P (canonicalOptional P))
      (mixedSourceSelected hT P (canonicalOptional P) S)
      (mixedSourceRootPool hT P (canonicalOptional P) S
        (fun _ : Fin C.card ↦ clusterCap)
        (mixedRichAllowed0 G cluster epsilon density D C)
        (fun _ : RemainingMinEdge
          (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
        (fun _ : ReservedEdge
          (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb)
        base0 Aalloc (fun e : RemainingMinEdge
          (R := regularityReducedGraph G cluster epsilon density) D C ↦ e.1)
        (fun e : ReservedEdge
          (R := regularityReducedGraph G cluster epsilon density) D ↦ e.1)
        (canonicalCoordinateOrientation G cluster epsilon density D C hT P
          (canonicalOptional P) S clusterCap base0 base1 baseb Aalloc mbSide))
      (mixedSourceInteriorPool hT P (canonicalOptional P) S
        (fun _ : Fin C.card ↦ clusterCap)
        (mixedRichAllowed0 G cluster epsilon density D C)
        (fun _ : RemainingMinEdge
          (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
        (fun _ : ReservedEdge
          (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb)
        base0 Aalloc
        (moutOriginalEdge
          (R := regularityReducedGraph G cluster epsilon density) D)
        (fun e : RemainingMinEdge
          (R := regularityReducedGraph G cluster epsilon density) D C ↦ e.1)
        (fun e : ReservedEdge
          (R := regularityReducedGraph G cluster epsilon density) D ↦ e.1)
        (canonicalCoordinateOrientation G cluster epsilon density D C hT P
          (canonicalOptional P) S clusterCap base0 base1 baseb Aalloc mbSide))
      (mixedSourcePairPool hT P (canonicalOptional P) S
        (fun _ : Fin C.card ↦ clusterCap)
        (mixedRichAllowed0 G cluster epsilon density D C)
        (fun _ : RemainingMinEdge
          (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
        (fun _ : ReservedEdge
          (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb)
        base0 Aalloc
        (moutOriginalEdge
          (R := regularityReducedGraph G cluster epsilon density) D)
        (fun e : RemainingMinEdge
          (R := regularityReducedGraph G cluster epsilon density) D C ↦ e.1)
        (fun e : ReservedEdge
          (R := regularityReducedGraph G cluster epsilon density) D ↦ e.1))
      (mixedSourceOrient hT P (canonicalOptional P)
        (canonicalCoordinateOrientation G cluster epsilon density D C hT P
          (canonicalOptional P) S clusterCap base0 base1 baseb Aalloc mbSide))
      (mixedRichWhole G cluster epsilon density Aroot Broot C)
      (mixedRichRawAfterRoot G cluster epsilon density C H.rootReserve
        H.companionReserve z)
      (epsilon : ℝ) (fun _ => (density : ℝ))
      (fun _ => (density : ℝ))) :
    T.IsContained G := by
  classical
  let optional := canonicalOptional P
  let orient := canonicalCoordinateOrientation G cluster epsilon density D C
    hT P optional S clusterCap base0 base1 baseb Aalloc mbSide
  let rootOnly := mixedSourceRootOnly hT P optional
  let selected := mixedSourceSelected hT P optional S
  let rootPool := mixedSourceRootPool hT P optional S
    (fun _ : Fin C.card ↦ clusterCap)
    (mixedRichAllowed0 G cluster epsilon density D C)
    (fun _ : RemainingMinEdge
      (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
    (fun _ : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb)
    base0 Aalloc (fun e : RemainingMinEdge
      (R := regularityReducedGraph G cluster epsilon density) D C ↦ e.1)
    (fun e : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D ↦ e.1) orient
  let interiorPool := mixedSourceInteriorPool hT P optional S
    (fun _ : Fin C.card ↦ clusterCap)
    (mixedRichAllowed0 G cluster epsilon density D C)
    (fun _ : RemainingMinEdge
      (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
    (fun _ : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb)
    base0 Aalloc
    (moutOriginalEdge
      (R := regularityReducedGraph G cluster epsilon density) D)
    (fun e : RemainingMinEdge
      (R := regularityReducedGraph G cluster epsilon density) D C ↦ e.1)
    (fun e : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D ↦ e.1) orient
  let pairPool := mixedSourcePairPool hT P optional S
    (fun _ : Fin C.card ↦ clusterCap)
    (mixedRichAllowed0 G cluster epsilon density D C)
    (fun _ : RemainingMinEdge
      (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
    (fun _ : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb)
    base0 Aalloc
    (moutOriginalEdge
      (R := regularityReducedGraph G cluster epsilon density) D)
    (fun e : RemainingMinEdge
      (R := regularityReducedGraph G cluster epsilon density) D C ↦ e.1)
    (fun e : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D ↦ e.1)
  let segmentOrient := mixedSourceOrient hT P optional orient
  let whole : RootSlot (Fin C.card) (MatchingEdge C67.M) → Finset B :=
    mixedRichWhole G cluster epsilon density Aroot Broot C
  let raw : RootSlot (Fin C.card) (MatchingEdge C67.M) → Finset B :=
    mixedRichRawAfterRoot G cluster epsilon density C H.rootReserve
      H.companionReserve z
  let relevant : RootSlot (Fin C.card) (MatchingEdge C67.M) → Prop :=
    RelevantSlot (G := G) (cluster := cluster)
    (epsilon := epsilon) (density := density) (D := D) (C := C)
  have hrootRelevant : ∀ i, relevant (rootPool i) := by
    intro i
    exact coordinateRootSlot_relevant G cluster epsilon density D C hT P
      optional S clusterCap base0 base1 baseb orient
      (mixedRichAllowed0 G cluster epsilon density D C) Aalloc i
  have hinteriorRelevant : ∀ i a, relevant (interiorPool i a) := by
    intro i a
    exact coordinateInteriorSlot_relevant G cluster epsilon density D C hT P
      optional S clusterCap base0 base1 baseb orient
      (mixedRichAllowed0 G cluster epsilon density D C) Aalloc i a
  have hrawSubset : ∀ p, raw p ⊆ whole p := by
    intro p
    exact Finset.sdiff_subset.trans
      (slotRaw_subset G cluster epsilon density D Aroot Broot C rhoK Pcluster
        threshold quota Gdegree H p)
  have hrawDisjoint : ∀ p q, relevant p → relevant q → p ≠ q →
      Disjoint (raw p) (raw q) := by
    intro p q hp hq hpq
    exact (slotRaw_disjoint_of_relevant_of_ne G cluster epsilon density D
      Aroot Broot C rhoK Pcluster threshold quota Gdegree H hCV1 p q hp hq
      hpq).mono Finset.sdiff_subset Finset.sdiff_subset
  have horiginalInj : Function.Injective (fun _ : Fin 1 => z) := by
    intro x y _
    exact Subsingleton.elim x y
  have hzOutside (p : RootSlot (Fin C.card) (MatchingEdge C67.M)) :
      z ∉ raw p := by
    intro hz
    exact (Finset.mem_sdiff.mp hz).2 (by simp)
  have huniformPair : ∀ i, ¬ rootOnly i →
      G.IsUniform (epsilon : ℝ) (whole (pairPool i 0))
        (whole (pairPool i 1)) := by
    intro i hi
    cases hclass : segmentSourceClass hT P optional i with
    | inl q =>
        exact False.elim (hi ((mem_rootSegments_iff hT P optional i).2
          ⟨q, hclass⟩))
    | inr j =>
        have hp := originalMatchingPair (C67 := C67) G cluster epsilon density
          (coordinateBranchEdge hT P optional S
            (fun _ : Fin C.card ↦ clusterCap)
            (mixedRichAllowed0 G cluster epsilon density D C)
            (fun _ : RemainingMinEdge
              (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
            (fun _ : ReservedEdge
              (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb)
            base0 Aalloc
            (moutOriginalEdge
              (R := regularityReducedGraph G cluster epsilon density) D)
            (fun e : RemainingMinEdge
              (R := regularityReducedGraph G cluster epsilon density) D C ↦ e.1)
            (fun e : ReservedEdge
              (R := regularityReducedGraph G cluster epsilon density) D ↦ e.1) j)
        simpa [whole, pairPool, mixedSourcePairPool, mixedCoordinatePairPool,
          mixedRichWhole, slotWhole, hclass] using
          (isUniform_real_of_rat G epsilon hp.1)
  have hwholeDisjoint : ∀ i, ¬ rootOnly i →
      Disjoint (whole (pairPool i 0)) (whole (pairPool i 1)) := by
    intro i hi
    cases hclass : segmentSourceClass hT P optional i with
    | inl q =>
        exact False.elim (hi ((mem_rootSegments_iff hT P optional i).2
          ⟨q, hclass⟩))
    | inr j =>
        let e := coordinateBranchEdge hT P optional S
          (fun _ : Fin C.card ↦ clusterCap)
          (mixedRichAllowed0 G cluster epsilon density D C)
          (fun _ : RemainingMinEdge
            (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
          (fun _ : ReservedEdge
            (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb)
          base0 Aalloc
          (moutOriginalEdge
            (R := regularityReducedGraph G cluster epsilon density) D)
          (fun e : RemainingMinEdge
            (R := regularityReducedGraph G cluster epsilon density) D C ↦ e.1)
          (fun e : ReservedEdge
            (R := regularityReducedGraph G cluster epsilon density) D ↦ e.1) j
        have hd := H.cluster_disjoint
          (matchingEdgeEndpoint e.1 0) (matchingEdgeEndpoint e.1 1)
          (matchingEndpoint_zero_ne_one G cluster epsilon density e)
        simpa [whole, pairPool, mixedSourcePairPool, mixedCoordinatePairPool,
          mixedRichWhole, slotWhole, hclass, e] using hd
  have hpairDensity : ∀ i, ¬ rootOnly i →
      (density : ℝ) ≤ G.edgeDensity (whole (pairPool i 0))
        (whole (pairPool i 1)) := by
    intro i hi
    cases hclass : segmentSourceClass hT P optional i with
    | inl q =>
        exact False.elim (hi ((mem_rootSegments_iff hT P optional i).2
          ⟨q, hclass⟩))
    | inr j =>
        have hp := originalMatchingPair (C67 := C67) G cluster epsilon density
          (coordinateBranchEdge hT P optional S
            (fun _ : Fin C.card ↦ clusterCap)
            (mixedRichAllowed0 G cluster epsilon density D C)
            (fun _ : RemainingMinEdge
              (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
            (fun _ : ReservedEdge
              (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb)
            base0 Aalloc
            (moutOriginalEdge
              (R := regularityReducedGraph G cluster epsilon density) D)
            (fun e : RemainingMinEdge
              (R := regularityReducedGraph G cluster epsilon density) D C ↦ e.1)
            (fun e : ReservedEdge
              (R := regularityReducedGraph G cluster epsilon density) D ↦ e.1) j)
        exact_mod_cast (show density ≤ G.edgeDensity
          (whole (pairPool i 0)) (whole (pairPool i 1)) by
            simpa [whole, pairPool, mixedSourcePairPool,
              mixedCoordinatePairPool, mixedRichWhole, slotWhole, hclass]
              using hp.2)
  have huniformSelected : ∀ i, ¬ rootOnly i → selected i →
      G.IsUniform (epsilon : ℝ) (whole (rootPool i))
        (whole (pairPool i (segmentOrient i 1))) := by
    intro i _ hi
    obtain ⟨j, hj, hclass⟩ :=
      (mem_F0Segments_iff hT P optional S i).1 hi
    have hp := canonicalSelectedAccessPair G Gdegree cluster epsilon density D
      Aroot Broot C rhoK Pcluster threshold quota H hT P optional S clusterCap
      base0 base1 baseb Aalloc mbSide j hj
    simpa [whole, rootPool, pairPool, segmentOrient, mixedSourceRootPool,
      mixedSourcePairPool, mixedSourceOrient, mixedCoordinatePairPool,
      mixedCoordinateOrient, mixedRichWhole, coordinateHierarchyRootSlot,
      coordinateBranchRootSlot, coordinateBranchEdge, slotWhole, orient,
      hclass, hj] using
        (isUniform_real_of_rat G epsilon hp.1)
  have hselectedDensity : ∀ i, ¬ rootOnly i → selected i →
      (density : ℝ) ≤ G.edgeDensity (whole (rootPool i))
        (whole (pairPool i (segmentOrient i 1))) := by
    intro i _ hi
    obtain ⟨j, hj, hclass⟩ :=
      (mem_F0Segments_iff hT P optional S i).1 hi
    have hp := canonicalSelectedAccessPair G Gdegree cluster epsilon density D
      Aroot Broot C rhoK Pcluster threshold quota H hT P optional S clusterCap
      base0 base1 baseb Aalloc mbSide j hj
    exact_mod_cast (show density ≤ G.edgeDensity
      (whole (rootPool i)) (whole (pairPool i (segmentOrient i 1))) by
        simpa [whole, rootPool, pairPool, segmentOrient, mixedSourceRootPool,
          mixedSourcePairPool, mixedSourceOrient, mixedCoordinatePairPool,
          mixedCoordinateOrient, mixedRichWhole, coordinateHierarchyRootSlot,
          coordinateBranchRootSlot, coordinateBranchEdge, slotWhole, orient,
          hclass, hj] using hp.2)
  let HF : MixedDynamicHostFacts
      (AllocationHierarchy hT P optional) G (fun _ : Fin 1 => z)
      rootOnly selected rootPool interiorPool pairPool segmentOrient whole raw
      relevant (epsilon : ℝ) (fun _ => (density : ℝ))
      (fun _ => (density : ℝ)) :=
    { raw_subset := hrawSubset
      root_relevant := hrootRelevant
      interior_relevant := hinteriorRelevant
      raw_disjoint := hrawDisjoint
      original_injective := horiginalInj
      original_outside_root := fun _ i => hzOutside (rootPool i)
      original_outside_interior := fun _ i a => hzOutside (interiorPool i a)
      uniform_pair := huniformPair
      whole_disjoint := hwholeDisjoint
      pair_density := hpairDensity
      uniform_selected_root := huniformSelected
      selected_root_density := hselectedDensity
      root_only_nonempty := R.root_only_nonempty
      available_large := R.available_large
      selected_root_large := R.selected_root_large
      selected_root_margin := R.selected_root_margin
      parent_neighbours := R.parent_neighbours
      pair_margin := R.pair_margin }
  exact isContained_of_mixedDynamicHostFacts hT P optional S
    (fun _ : Fin C.card ↦ clusterCap)
    (mixedRichAllowed0 G cluster epsilon density D C)
    (fun _ : RemainingMinEdge
      (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
    (fun _ : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb)
    base0 Aalloc
    (moutOriginalEdge
      (R := regularityReducedGraph G cluster epsilon density) D)
    (fun e : RemainingMinEdge
      (R := regularityReducedGraph G cluster epsilon density) D C ↦ e.1)
    (fun e : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D ↦ e.1)
    orient G z whole raw relevant (epsilon : ℝ)
    (fun _ => (density : ℝ)) (fun _ => (density : ℝ))
    (canonicalOptional_parity hT P) HF

end Erdos547b.ZhaoClaim616RichCoordinateMixedDynamicApplication

#print axioms Erdos547b.ZhaoClaim616RichCoordinateMixedDynamicApplication.isContained_of_richMixedDynamicResidualFacts
