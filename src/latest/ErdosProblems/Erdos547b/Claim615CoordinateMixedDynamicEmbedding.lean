/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615CoordinateMixedDynamicLayout
import ErdosProblems.Erdos547b.Claim616CoordinateMixedDynamicEmbedding
import ErdosProblems.Erdos547b.Lemma614HierarchicalUnifiedFullTree

/-!
# Cut-aware mixed dynamic embedding for Claim 6.15

This is the source-specialized endpoint of the mixed online hierarchy.  It
keeps the canonical optional cut-parent segmentation, uses no distinguished
branch marks, and constructs a literal copy of the original tree from the
regular-pair and residual-cardinality facts of the dynamic local steps.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim615CoordinateMixedDynamicEmbedding

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim616CoordinateMixedDynamicEmbedding
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim615CoordinateSourceAllocation
open Erdos547b.ZhaoClaim615HierarchicalCoordinateSourceLayout
open Erdos547b.ZhaoClaim615CoordinateMixedDynamicLayout
open Erdos547b.ZhaoLemma59Hierarchical
open Erdos547b.ZhaoLemma59HierarchicalOnline
open Erdos547b.ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalCoordinateMixedDynamicOnline
open Erdos547b.ZhaoLemma59HierarchicalCoordinateMixedDynamicOnline.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma614HierarchicalFullTree
open Erdos547b.ZhaoLemma614HierarchicalUnifiedFullTree

universe u v x

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small target slack : ℕ}

section Source

variable
    {K0 K1 Kb Edge : Type*}
    [Fintype K0] [DecidableEq K0]
    [Fintype K1] [DecidableEq K1]
    [Fintype Kb] [DecidableEq Kb]
    [DecidableEq Edge]

variable
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    {available : Finset
      (ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)}
    (S : SelectedF0 P available target slack)
    (capacity0 : K0 → ℕ) (capacity1 : K1 → ℕ) (capacityb : Kb → ℕ)
    (A : SourceAllocation P S K0 K1 Kb capacity0 capacity1 capacityb)
    (edge0 : K0 → Edge) (edge1 : K1 → Edge) (edgeb : Kb → Edge)
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)

abbrev mixedSourceRootPool :=
  coordinateHierarchyRootSlot hT P optional ∅ (sourceVertexReservoirSide P) S
    capacity0 capacity1 capacityb A edge0 edge1 edgeb orient

abbrev mixedSourceInteriorPool :=
  coordinateHierarchyInteriorSlot hT P optional S capacity0 capacity1
    capacityb A edge0 edge1 edgeb orient

abbrev mixedSourcePairPool :=
  mixedCoordinatePairPool hT P optional S capacity0 capacity1 capacityb A
    edge0 edge1 edgeb

abbrev mixedSourceOrient := mixedCoordinateOrient hT P optional orient

abbrev mixedSourceRootOnly := mixedCoordinateRootOnly hT P optional

abbrev mixedSourceSelected := mixedCoordinateSelected hT P optional

/-- The Claim 6.15 mixed dynamic local steps produce a literal copy of the
original tree.  No copy or continuation datum occurs in the input record. -/
theorem isContained_of_mixedDynamicHostFacts
    {B : Type v} [Fintype B] [DecidableEq B]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (z : B) (whole raw : RootSlot Edge → Finset B)
    (relevant : RootSlot Edge → Prop)
    (rho : ℝ)
    (rootDensity pairDensity : SegmentIndex hT P optional → ℝ)
    (hparity : OptionalBranchRootParity P optional)
    (H : MixedDynamicHostFacts (AllocationHierarchy hT P optional) G
      (fun _ : Fin 1 => z)
      (mixedSourceRootOnly hT P optional)
      (mixedSourceSelected hT P optional)
      (mixedSourceRootPool hT P optional S capacity0 capacity1 capacityb A
        edge0 edge1 edgeb orient)
      (mixedSourceInteriorPool hT P optional S capacity0 capacity1 capacityb A
        edge0 edge1 edgeb orient)
      (mixedSourcePairPool hT P optional S capacity0 capacity1 capacityb A
        edge0 edge1 edgeb)
      (mixedSourceOrient hT P optional orient)
      whole raw relevant rho rootDensity pairDensity) :
    T.IsContained G := by
  classical
  let F := AllocationHierarchy hT P optional
  let rootOnly := mixedSourceRootOnly hT P optional
  let selected := mixedSourceSelected hT P optional
  let rootPool := mixedSourceRootPool hT P optional S capacity0 capacity1
    capacityb A edge0 edge1 edgeb orient
  let interiorPool := mixedSourceInteriorPool hT P optional S capacity0
    capacity1 capacityb A edge0 edge1 edgeb orient
  let pairPool := mixedSourcePairPool hT P optional S capacity0 capacity1
    capacityb A edge0 edge1 edgeb
  let segmentOrient := mixedSourceOrient hT P optional orient
  have hrootPair : ∀ i, ¬ rootOnly i → ¬ selected i →
      rootPool i = pairPool i (segmentOrient i 0) := by
    intro i hr _hs
    exact mixedCoordinateRootPair hT P optional S capacity0 capacity1
      capacityb A edge0 edge1 edgeb orient hparity i hr
  have hinteriorPair : ∀ i a,
      interiorPool i a = pairPool i
        (segmentOrient i ((F.segments.isTree i).coloringTwoOfVert
          (F.segments.root i) a)) := by
    intro i a
    exact mixedCoordinateInteriorPair hT P optional S capacity0 capacity1
      capacityb A edge0 edge1 edgeb orient hparity i a
  have hrootOnlySize : ∀ i, rootOnly i → F.segments.size i = 1 := by
    intro i hi
    exact mixedCoordinateRootOnly_size hT P optional i hi
  obtain ⟨E⟩ := exists_hierarchicalCandidateEmbedding_mixedDynamic F G
    (fun _ : Fin 1 => z) rootOnly selected rootPool interiorPool pairPool
    segmentOrient whole raw rho rootDensity pairDensity hrootPair
    hinteriorPair H.raw_subset relevant H.root_relevant H.interior_relevant
    H.raw_disjoint H.original_injective H.original_outside_root
    H.original_outside_interior H.uniform_pair H.whole_disjoint H.pair_density
    H.uniform_selected_root H.selected_root_density hrootOnlySize
    H.root_only_nonempty H.available_large H.selected_root_large
    H.selected_root_margin H.parent_neighbours H.pair_margin
  let Efull := fullTreeRegularEmbeddingOfHierarchyEmbedding T hT globalRoot
    (AllocationSpecial hT P optional) G (fun _ : Fin 1 => z)
      (mixedRootCandidate rootPool raw)
      (mixedInteriorCandidate F interiorPool raw) E
  exact Efull.fullCopy.isContained

end Source

end Erdos547b.ZhaoClaim615CoordinateMixedDynamicEmbedding

#print axioms Erdos547b.ZhaoClaim615CoordinateMixedDynamicEmbedding.isContained_of_mixedDynamicHostFacts
