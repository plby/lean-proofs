/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615CoordinateMixedDynamicEmbedding
import ErdosProblems.Erdos547b.Claim615RichCoordinatePairFacts
import ErdosProblems.Erdos547b.Claim615HierarchicalCoordinateHostPools

/-!
# Rich-host mixed dynamic application for Claim 6.15

All static pool inclusion, separation, matching-pair uniformity, and density
facts are derived from the literal rich host.  The caller supplies only the
prefix-dependent inequalities in `MixedDynamicResidualFacts`; no copy,
embedding, or continuation is an input.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim615RichCoordinateMixedDynamicApplication

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim615CoordinateSourceAllocation
open Erdos547b.ZhaoClaim615HierarchicalCoordinateSourceLayout
open Erdos547b.ZhaoClaim615HierarchicalCoordinateHostPools
open Erdos547b.ZhaoClaim615RichCoordinatePairFacts
open Erdos547b.ZhaoClaim615CoordinateMixedDynamicLayout
open Erdos547b.ZhaoClaim615CoordinateMixedDynamicEmbedding
open Erdos547b.ZhaoLemma59HierarchicalCoordinateMixedDynamicOnline.HierarchicalSegmentForest
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoSection6Dichotomy

universe u v w

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small target slack : ℕ}

variable {Bv : Type v} {I : Type w}
variable [Fintype Bv] [DecidableEq Bv] [Fintype I] [DecidableEq I]
variable (Pcluster : ClusterAssignment Bv I)
variable (Gdegree : SimpleGraph Bv) [DecidableRel Gdegree.Adj]
variable (threshold quota : ℕ)
variable (R : SimpleGraph I) [DecidableRel R.Adj]
variable (miss : ℕ)
variable
  (Q : RichClaim61Certificate Pcluster Gdegree threshold quota R
    (largeClustersAtLeast Pcluster Gdegree threshold quota) miss)

/-- Delete the already embedded global root from every literal rich pool. -/
abbrev mixedRichRawAfterRoot (z : Bv)
    (p : RootSlot (MatchingEdge Q.claim67.M)) : Finset Bv :=
  slotRaw Pcluster Gdegree threshold quota R miss Q p \ {z}

private theorem matchingEndpoint_zero_ne_one
    (e : MatchingEdge Q.claim67.M) :
    matchingEdgeEndpoint e.1 0 ≠ matchingEdgeEndpoint e.1 1 := by
  exact (matchingEdgeEndpoint_adj Q.claim67.M e.1 e.2).ne

section Source

/-- Concrete rich-host realization through the mixed dynamic hierarchy. -/
theorem isContained_of_richMixedDynamicResidualFacts
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    {available : Finset
      (ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)}
    (S : SelectedF0 P available target slack)
    {K0 K1 Kb : Type*}
    [Fintype K0] [DecidableEq K0]
    [Fintype K1] [DecidableEq K1]
    [Fintype Kb] [DecidableEq Kb]
    (capacity0 : K0 → ℕ) (capacity1 : K1 → ℕ) (capacityb : Kb → ℕ)
    (A : SourceAllocation P S K0 K1 Kb capacity0 capacity1 capacityb)
    (edge0 : K0 → MatchingEdge Q.claim67.M)
    (edge1 : K1 → MatchingEdge Q.claim67.M)
    (edgeb : Kb → MatchingEdge Q.claim67.M)
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rho density : ℝ)
    (Hpair : ReducedPairRealization Pcluster R G rho density)
    (hparity : OptionalBranchRootParity P optional)
    (z : Bv)
    (Hres : Erdos547b.ZhaoClaim616CoordinateMixedDynamicEmbedding.MixedDynamicResidualFacts
      (AllocationHierarchy hT P optional) G (fun _ : Fin 1 => z)
      (mixedSourceRootOnly hT P optional)
      (mixedSourceSelected hT P optional)
      (mixedSourceRootPool hT P optional S capacity0 capacity1 capacityb A
        edge0 edge1 edgeb orient)
      (mixedSourceInteriorPool hT P optional S capacity0 capacity1 capacityb A
        edge0 edge1 edgeb orient)
      (mixedSourcePairPool hT P optional S capacity0 capacity1 capacityb A
        edge0 edge1 edgeb)
      (mixedSourceOrient hT P optional orient)
      (slotWhole Pcluster Gdegree threshold quota R miss Q)
      (mixedRichRawAfterRoot Pcluster Gdegree threshold quota R miss Q z)
      rho (fun _ => density) (fun _ => density)) :
    T.IsContained G := by
  classical
  let rootOnly := mixedSourceRootOnly hT P optional
  let selected := mixedSourceSelected hT P optional
  let rootPool := mixedSourceRootPool hT P optional S capacity0 capacity1
    capacityb A edge0 edge1 edgeb orient
  let interiorPool := mixedSourceInteriorPool hT P optional S capacity0
    capacity1 capacityb A edge0 edge1 edgeb orient
  let pairPool := mixedSourcePairPool hT P optional S capacity0 capacity1
    capacityb A edge0 edge1 edgeb
  let segmentOrient := mixedSourceOrient hT P optional orient
  let whole := slotWhole Pcluster Gdegree threshold quota R miss Q
  let raw := mixedRichRawAfterRoot Pcluster Gdegree threshold quota R miss Q z
  let relevant : RootSlot (MatchingEdge Q.claim67.M) → Prop := fun _ => True
  have hrawSubset : ∀ p, raw p ⊆ whole p := by
    intro p
    exact Finset.sdiff_subset.trans
      (slotRaw_subset_slotWhole Pcluster Gdegree threshold quota R miss Q p)
  have hrawDisjoint : ∀ p q, relevant p → relevant q → p ≠ q →
      Disjoint (raw p) (raw q) := by
    intro p q _ _ hpq
    exact (slotRaw_disjoint_of_ne Pcluster Gdegree threshold quota R miss Q
      p q hpq).mono Finset.sdiff_subset Finset.sdiff_subset
  have horiginalInj : Function.Injective (fun _ : Fin 1 => z) := by
    intro x y _
    exact Subsingleton.elim x y
  have hzOutside (p : RootSlot (MatchingEdge Q.claim67.M)) : z ∉ raw p := by
    intro hz
    exact (Finset.mem_sdiff.mp hz).2 (by simp)
  have huniformPair : ∀ i, ¬ rootOnly i →
      G.IsUniform rho (whole (pairPool i 0)) (whole (pairPool i 1)) := by
    intro i hi
    cases hclass : segmentSourceClass hT P optional i with
    | inl q =>
        exfalso
        apply hi
        change i ∈ rootSegments hT P optional
        exact (mem_rootSegments_iff hT P optional i).2 ⟨q, hclass⟩
    | inr j =>
        let e := coordinateBranchEdge P S capacity0 capacity1 capacityb A
          edge0 edge1 edgeb j
        have hadj : (padGraph R).Adj
            (matchingEdgeEndpoint e.1 0) (matchingEdgeEndpoint e.1 1) :=
          matchingEdgeEndpoint_adj Q.claim67.M e.1 e.2
        have hp := Hpair.pair_of_adj _ _ hadj
        simpa [whole, pairPool, mixedSourcePairPool, mixedCoordinatePairPool,
          slotWhole, richSlotVertex, hclass, e] using hp.1
  have hwholeDisjoint : ∀ i, ¬ rootOnly i →
      Disjoint (whole (pairPool i 0)) (whole (pairPool i 1)) := by
    intro i hi
    cases hclass : segmentSourceClass hT P optional i with
    | inl q =>
        exfalso
        apply hi
        change i ∈ rootSegments hT P optional
        exact (mem_rootSegments_iff hT P optional i).2 ⟨q, hclass⟩
    | inr j =>
        let e := coordinateBranchEdge P S capacity0 capacity1 capacityb A
          edge0 edge1 edgeb j
        have hd := clusterVertices_disjoint (padAssignment Pcluster)
          (matchingEndpoint_zero_ne_one Pcluster Gdegree threshold quota R miss
            Q e)
        simpa [whole, pairPool, mixedSourcePairPool, mixedCoordinatePairPool,
          slotWhole, richSlotVertex, clusterVertices_padAssignment, hclass, e]
          using hd
  have hpairDensity : ∀ i, ¬ rootOnly i →
      density ≤ G.edgeDensity (whole (pairPool i 0))
        (whole (pairPool i 1)) := by
    intro i hi
    cases hclass : segmentSourceClass hT P optional i with
    | inl q =>
        exfalso
        apply hi
        change i ∈ rootSegments hT P optional
        exact (mem_rootSegments_iff hT P optional i).2 ⟨q, hclass⟩
    | inr j =>
        let e := coordinateBranchEdge P S capacity0 capacity1 capacityb A
          edge0 edge1 edgeb j
        have hadj : (padGraph R).Adj
            (matchingEdgeEndpoint e.1 0) (matchingEdgeEndpoint e.1 1) :=
          matchingEdgeEndpoint_adj Q.claim67.M e.1 e.2
        have hp := Hpair.pair_of_adj _ _ hadj
        simpa [whole, pairPool, mixedSourcePairPool, mixedCoordinatePairPool,
          slotWhole, richSlotVertex, hclass, e] using hp.2
  have huniformSelected : ∀ i, ¬ rootOnly i → selected i →
      G.IsUniform rho (whole (rootPool i))
        (whole (pairPool i (segmentOrient i 1))) := by
    intro i _ hi
    change False at hi
    exact hi.elim
  have hselectedDensity : ∀ i, ¬ rootOnly i → selected i →
      density ≤ G.edgeDensity (whole (rootPool i))
        (whole (pairPool i (segmentOrient i 1))) := by
    intro i _ hi
    change False at hi
    exact hi.elim
  let HF : Erdos547b.ZhaoClaim616CoordinateMixedDynamicEmbedding.MixedDynamicHostFacts
      (AllocationHierarchy hT P optional) G (fun _ : Fin 1 => z)
      rootOnly selected rootPool interiorPool pairPool segmentOrient whole raw
      relevant rho (fun _ => density) (fun _ => density) :=
    { raw_subset := hrawSubset
      root_relevant := fun _ => trivial
      interior_relevant := fun _ _ => trivial
      raw_disjoint := hrawDisjoint
      original_injective := horiginalInj
      original_outside_root := fun _ i => hzOutside (rootPool i)
      original_outside_interior := fun _ i a => hzOutside (interiorPool i a)
      uniform_pair := huniformPair
      whole_disjoint := hwholeDisjoint
      pair_density := hpairDensity
      uniform_selected_root := huniformSelected
      selected_root_density := hselectedDensity
      root_only_nonempty := Hres.root_only_nonempty
      available_large := Hres.available_large
      selected_root_large := Hres.selected_root_large
      selected_root_margin := Hres.selected_root_margin
      parent_neighbours := Hres.parent_neighbours
      pair_margin := Hres.pair_margin }
  exact Erdos547b.ZhaoClaim615CoordinateMixedDynamicEmbedding.isContained_of_mixedDynamicHostFacts
    hT P optional S capacity0 capacity1 capacityb A edge0 edge1 edgeb orient G
      z whole raw relevant rho (fun _ => density) (fun _ => density) hparity HF

end Source

end Erdos547b.ZhaoClaim615RichCoordinateMixedDynamicApplication

#print axioms Erdos547b.ZhaoClaim615RichCoordinateMixedDynamicApplication.isContained_of_richMixedDynamicResidualFacts
