/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616CoordinateMixedDynamicLayout
import ErdosProblems.Erdos547b.Lemma614HierarchicalUnifiedFullTree

/-!
# Cut-aware mixed dynamic embedding for Claim 6.16

This is the source-specialized endpoint of the mixed dynamic hierarchy.  Its
fact record contains only literal regular-pair and residual-set obligations.
The theorem constructs the hierarchy copy internally and then transports it
back to a copy of the original tree.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim616CoordinateMixedDynamicEmbedding

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim616HierarchicalAllocation
open Erdos547b.ZhaoClaim616HierarchicalSourceLayout
open Erdos547b.ZhaoClaim616HierarchicalCoordinateSourceLayout
open Erdos547b.ZhaoClaim616CoordinateMixedDynamicLayout
open Erdos547b.ZhaoLemma59Hierarchical
open Erdos547b.ZhaoLemma59HierarchicalOnline
open Erdos547b.ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalCoordinateMixedDynamicOnline
open Erdos547b.ZhaoLemma59HierarchicalCoordinateMixedDynamicOnline.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma614HierarchicalFullTree
open Erdos547b.ZhaoLemma614HierarchicalUnifiedFullTree

universe u v

/-- The exact graph and residual-cardinality obligations used by the mixed
dynamic hierarchy constructor.  It contains no copy or embedding datum. -/
structure MixedDynamicHostFacts
    {r s : ℕ} {B : Type u} {Pool : Type v}
    [Fintype B] [DecidableEq B] [DecidableEq Pool]
    (F : HierarchicalSegmentForest r s)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (originalImage : Fin r → B)
    (rootOnly selected : Fin s → Prop)
    (rootPool : Fin s → Pool)
    (interiorPool : (i : Fin s) → Fin (F.segments.size i) → Pool)
    (pairPool : Fin s → Fin 2 → Pool)
    (orient : Fin s → Fin 2 ≃ Fin 2)
    (whole raw : Pool → Finset B) (relevant : Pool → Prop)
    (rho : ℝ) (rootDensity pairDensity : Fin s → ℝ) : Prop where
  raw_subset : ∀ p, raw p ⊆ whole p
  root_relevant : ∀ i, relevant (rootPool i)
  interior_relevant : ∀ i a, relevant (interiorPool i a)
  raw_disjoint : ∀ p q, relevant p → relevant q → p ≠ q →
    Disjoint (raw p) (raw q)
  original_injective : Function.Injective originalImage
  original_outside_root : ∀ q i,
    originalImage q ∉ mixedRootCandidate rootPool raw i
  original_outside_interior : ∀ q i a,
    originalImage q ∉ mixedInteriorCandidate F interiorPool raw i a
  uniform_pair : ∀ i, ¬ rootOnly i →
    G.IsUniform rho (whole (pairPool i 0)) (whole (pairPool i 1))
  whole_disjoint : ∀ i, ¬ rootOnly i →
    Disjoint (whole (pairPool i 0)) (whole (pairPool i 1))
  pair_density : ∀ i, ¬ rootOnly i →
    pairDensity i ≤ G.edgeDensity
      (whole (pairPool i 0)) (whole (pairPool i 1))
  uniform_selected_root : ∀ i, ¬ rootOnly i → selected i →
    G.IsUniform rho (whole (rootPool i))
      (whole (pairPool i (orient i 1)))
  selected_root_density : ∀ i, ¬ rootOnly i → selected i →
    rootDensity i ≤ G.edgeDensity (whole (rootPool i))
      (whole (pairPool i (orient i 1)))
  root_only_nonempty : ∀ i
      (prior : ∀ j : Fin s, j.val < i.val →
        SegmentRealization F G (mixedRootCandidate rootPool raw)
          (mixedInteriorCandidate F interiorPool raw) j),
    rootOnly i →
    (mixedSelectedRootAvailable F G originalImage rootPool interiorPool raw i
      prior).Nonempty
  available_large : ∀ i
      (prior : ∀ j : Fin s, j.val < i.val →
        SegmentRealization F G (mixedRootCandidate rootPool raw)
          (mixedInteriorCandidate F interiorPool raw) j) c,
    ¬ rootOnly i →
    rho * (#(whole (pairPool i c)) : ℝ) ≤
      (#(mixedAvailable F G rootPool interiorPool pairPool raw i c prior) : ℝ)
  selected_root_large : ∀ i
      (prior : ∀ j : Fin s, j.val < i.val →
        SegmentRealization F G (mixedRootCandidate rootPool raw)
          (mixedInteriorCandidate F interiorPool raw) j),
    ¬ rootOnly i → selected i →
    rho * (#(whole (rootPool i)) : ℝ) <
      (#(mixedSelectedRootAvailable F G originalImage rootPool interiorPool
        raw i prior) : ℝ)
  selected_root_margin : ∀ i
      (prior : ∀ j : Fin s, j.val < i.val →
        SegmentRealization F G (mixedRootCandidate rootPool raw)
          (mixedInteriorCandidate F interiorPool raw) j),
    ¬ rootOnly i → selected i →
    (F.segments.size i : ℝ) +
        rho * (#(whole (pairPool i (orient i 1))) : ℝ) ≤
      (rootDensity i - rho) *
        (#(mixedAvailable F G rootPool interiorPool pairPool raw i
          (orient i 1) prior) : ℝ)
  parent_neighbours : ∀ i
      (prior : ∀ j : Fin s, j.val < i.val →
        SegmentRealization F G (mixedRootCandidate rootPool raw)
          (mixedInteriorCandidate F interiorPool raw) j),
    ¬ rootOnly i → ¬ selected i →
    1 + rho * (#(whole (pairPool i (orient i 0))) : ℝ) ≤
      (#((mixedAvailable F G rootPool interiorPool pairPool raw i
        (orient i 0) prior).filter
          (G.Adj (mixedParentImage F G originalImage rootPool interiorPool raw
            i prior))) : ℝ)
  pair_margin : ∀ i
      (prior : ∀ j : Fin s, j.val < i.val →
        SegmentRealization F G (mixedRootCandidate rootPool raw)
          (mixedInteriorCandidate F interiorPool raw) j) c,
    ¬ rootOnly i →
    (F.segments.size i : ℝ) + rho * (#(whole (pairPool i c)) : ℝ) + 1 ≤
      (pairDensity i - rho) *
        (#(mixedAvailable F G rootPool interiorPool pairPool raw i c prior) : ℝ)

/-- The genuinely dynamic part of `MixedDynamicHostFacts`.  These are the
six residual-set inequalities that depend on the already embedded prefix;
all static pool, separation, and regular-pair fields can be supplied by a
concrete host layout. -/
structure MixedDynamicResidualFacts
    {r s : ℕ} {B : Type u} {Pool : Type v}
    [Fintype B] [DecidableEq B] [DecidableEq Pool]
    (F : HierarchicalSegmentForest r s)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (originalImage : Fin r → B)
    (rootOnly selected : Fin s → Prop)
    (rootPool : Fin s → Pool)
    (interiorPool : (i : Fin s) → Fin (F.segments.size i) → Pool)
    (pairPool : Fin s → Fin 2 → Pool)
    (orient : Fin s → Fin 2 ≃ Fin 2)
    (whole raw : Pool → Finset B)
    (rho : ℝ) (rootDensity pairDensity : Fin s → ℝ) : Prop where
  root_only_nonempty : ∀ i
      (prior : ∀ j : Fin s, j.val < i.val →
        SegmentRealization F G (mixedRootCandidate rootPool raw)
          (mixedInteriorCandidate F interiorPool raw) j),
    rootOnly i →
    (mixedSelectedRootAvailable F G originalImage rootPool interiorPool raw i
      prior).Nonempty
  available_large : ∀ i
      (prior : ∀ j : Fin s, j.val < i.val →
        SegmentRealization F G (mixedRootCandidate rootPool raw)
          (mixedInteriorCandidate F interiorPool raw) j) c,
    ¬ rootOnly i →
    rho * (#(whole (pairPool i c)) : ℝ) ≤
      (#(mixedAvailable F G rootPool interiorPool pairPool raw i c prior) : ℝ)
  selected_root_large : ∀ i
      (prior : ∀ j : Fin s, j.val < i.val →
        SegmentRealization F G (mixedRootCandidate rootPool raw)
          (mixedInteriorCandidate F interiorPool raw) j),
    ¬ rootOnly i → selected i →
    rho * (#(whole (rootPool i)) : ℝ) <
      (#(mixedSelectedRootAvailable F G originalImage rootPool interiorPool
        raw i prior) : ℝ)
  selected_root_margin : ∀ i
      (prior : ∀ j : Fin s, j.val < i.val →
        SegmentRealization F G (mixedRootCandidate rootPool raw)
          (mixedInteriorCandidate F interiorPool raw) j),
    ¬ rootOnly i → selected i →
    (F.segments.size i : ℝ) +
        rho * (#(whole (pairPool i (orient i 1))) : ℝ) ≤
      (rootDensity i - rho) *
        (#(mixedAvailable F G rootPool interiorPool pairPool raw i
          (orient i 1) prior) : ℝ)
  parent_neighbours : ∀ i
      (prior : ∀ j : Fin s, j.val < i.val →
        SegmentRealization F G (mixedRootCandidate rootPool raw)
          (mixedInteriorCandidate F interiorPool raw) j),
    ¬ rootOnly i → ¬ selected i →
    1 + rho * (#(whole (pairPool i (orient i 0))) : ℝ) ≤
      (#((mixedAvailable F G rootPool interiorPool pairPool raw i
        (orient i 0) prior).filter
          (G.Adj (mixedParentImage F G originalImage rootPool interiorPool raw
            i prior))) : ℝ)
  pair_margin : ∀ i
      (prior : ∀ j : Fin s, j.val < i.val →
        SegmentRealization F G (mixedRootCandidate rootPool raw)
          (mixedInteriorCandidate F interiorPool raw) j) c,
    ¬ rootOnly i →
    (F.segments.size i : ℝ) + rho * (#(whole (pairPool i c)) : ℝ) + 1 ≤
      (pairDensity i - rho) *
        (#(mixedAvailable F G rootPool interiorPool pairPool raw i c prior) : ℝ)

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small target slack : ℕ}

section Source

variable
    {CIndex K0 K1 Kb Edge : Type*}
    [Fintype CIndex] [DecidableEq CIndex]
    [Fintype K0] [DecidableEq K0]
    [Fintype K1] [DecidableEq K1]
    [Fintype Kb] [DecidableEq Kb]
    [DecidableEq Edge]

variable
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCapacity : CIndex → ℕ)
    (allowed0 : CIndex → Finset K0)
    (capacity1 : K1 → ℕ) (capacityb : Kb → ℕ) (base0 : ℕ)
    (A : SourceSegmentAllocation hT P optional S clusterCapacity allowed0
      capacity1 capacityb base0)
    (edge0 : K0 → Edge) (edge1 : K1 → Edge) (edgeb : Kb → Edge)
    (orient : BranchIndex P → Fin 2 ≃ Fin 2)

abbrev mixedSourceRootPool :=
  coordinateHierarchyRootSlot hT P optional S clusterCapacity allowed0
    capacity1 capacityb base0 A edge1 edgeb orient

abbrev mixedSourceInteriorPool :=
  coordinateHierarchyInteriorSlot hT P optional S clusterCapacity allowed0
    capacity1 capacityb base0 A edge0 edge1 edgeb orient

abbrev mixedSourcePairPool :=
  mixedCoordinatePairPool hT P optional S clusterCapacity allowed0 capacity1
    capacityb base0 A edge0 edge1 edgeb

abbrev mixedSourceOrient := mixedCoordinateOrient hT P optional orient

abbrev mixedSourceRootOnly := mixedCoordinateRootOnly hT P optional

abbrev mixedSourceSelected := mixedCoordinateSelected hT P optional S

/-- The mixed dynamic local steps produce a literal copy of the original
tree. -/
theorem isContained_of_mixedDynamicHostFacts
    {B : Type v} [Fintype B] [DecidableEq B]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (z : B) (whole raw : RootSlot CIndex Edge → Finset B)
    (relevant : RootSlot CIndex Edge → Prop)
    (rho : ℝ)
    (rootDensity pairDensity : SegmentIndex hT P optional → ℝ)
    (hparity : OptionalBranchRootParity P optional)
    (H : MixedDynamicHostFacts (AllocationHierarchy hT P optional) G
      (fun _ : Fin 1 => z)
      (mixedSourceRootOnly hT P optional)
      (mixedSourceSelected hT P optional S)
      (mixedSourceRootPool hT P optional S clusterCapacity allowed0 capacity1
        capacityb base0 A edge1 edgeb orient)
      (mixedSourceInteriorPool hT P optional S clusterCapacity allowed0
        capacity1 capacityb base0 A edge0 edge1 edgeb orient)
      (mixedSourcePairPool hT P optional S clusterCapacity allowed0 capacity1
        capacityb base0 A edge0 edge1 edgeb)
      (mixedSourceOrient hT P optional orient)
      whole raw relevant rho rootDensity pairDensity) :
    T.IsContained G := by
  classical
  let F := AllocationHierarchy hT P optional
  let rootOnly := mixedSourceRootOnly hT P optional
  let selected := mixedSourceSelected hT P optional S
  let rootPool := mixedSourceRootPool hT P optional S clusterCapacity allowed0
    capacity1 capacityb base0 A edge1 edgeb orient
  let interiorPool := mixedSourceInteriorPool hT P optional S clusterCapacity
    allowed0 capacity1 capacityb base0 A edge0 edge1 edgeb orient
  let pairPool := mixedSourcePairPool hT P optional S clusterCapacity allowed0
    capacity1 capacityb base0 A edge0 edge1 edgeb
  let segmentOrient := mixedSourceOrient hT P optional orient
  have hrootPair : ∀ i, ¬ rootOnly i → ¬ selected i →
      rootPool i = pairPool i (segmentOrient i 0) := by
    intro i hr hs
    exact mixedCoordinateRootPair hT P optional S clusterCapacity allowed0
      capacity1 capacityb base0 A edge0 edge1 edgeb orient i hr hs
  have hinteriorPair : ∀ i a,
      interiorPool i a = pairPool i
        (segmentOrient i ((F.segments.isTree i).coloringTwoOfVert
          (F.segments.root i) a)) := by
    intro i a
    exact mixedCoordinateInteriorPair hT P optional S clusterCapacity allowed0
      capacity1 capacityb base0 A edge0 edge1 edgeb orient hparity i a
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

end Erdos547b.ZhaoClaim616CoordinateMixedDynamicEmbedding

#print axioms Erdos547b.ZhaoClaim616CoordinateMixedDynamicEmbedding.isContained_of_mixedDynamicHostFacts
