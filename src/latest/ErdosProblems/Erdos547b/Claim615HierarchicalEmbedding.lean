/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615HierarchicalSourceLayout
import ErdosProblems.Erdos547b.HierarchicalTargetUnifiedApplication
import ErdosProblems.Erdos547b.Lemma614HierarchicalUnifiedFullTree

/-!
# The no-C hierarchical realization in Zhao Lemma 6.15

The source layout in `Claim615HierarchicalSourceLayout` assigns the selected
exceptional forest and the two residual forests directly to oriented
matching pairs.  This file feeds that literal layout to the target-relative
hierarchical constructor and transports the resulting hierarchy copy back to
the original tree.  No cut-forest copy, deleted-edge adjacency, continuation,
or containment conclusion is an input.

`TargetUnifiedHostFacts` is an intermediate bundle of the primitive regular
pair and capacity facts consumed by the generic constructor.  The rich
Claim-6.15 application constructs this bundle from the degree-form clusters,
the selected exceptional submatching, and Zhao Lemma 5.8(2)/(3).
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615HierarchicalEmbedding

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoLemma59Hierarchical
open Erdos547b.ZhaoLemma59HierarchicalRegular
open Erdos547b.ZhaoLemma59HierarchicalTargetCleaning
open Erdos547b.ZhaoLemma59HierarchicalTargetUnifiedApplication
open Erdos547b.ZhaoLemma614HierarchicalFullTree
open Erdos547b.ZhaoLemma614HierarchicalUnifiedFullTree
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim615HierarchicalSourceLayout

universe u v

/-- Primitive graph-side facts required by the target-relative hierarchy
constructor.  This record contains only subsets, uniform pairs, densities,
finite loads, and disjointness. -/
structure TargetUnifiedHostFacts
    {s : ℕ} {B RootSlot Pool : Type*}
    [Fintype B] [DecidableEq B] [DecidableEq Pool]
    (F : HierarchicalSegmentForest 1 s)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho density : ℝ)
    (sourceWhole sourceRaw : Finset B)
    (rootSlot : Fin s → RootSlot)
    (interiorSlot : (i : Fin s) → Fin (F.segments.size i) → RootSlot)
    (slotPool : RootSlot → Pool)
    (rootWhole rootRaw : RootSlot → Finset B)
    (poolCapacity : Pool → ℕ) (removalBudget : ℝ) where
  interior_pool : ∀ i a,
    slotPool (interiorSlot i a) =
      slotPool (interiorSlot i (F.segments.root i))
  source_subset : sourceRaw ⊆ sourceWhole
  source_large : rho * #sourceWhole ≤ #sourceRaw
  root_raw_subset : ∀ i,
    rootRaw (rootSlot i) ⊆ rootWhole (rootSlot i)
  interior_raw_subset : ∀ i a,
    rootRaw (interiorSlot i a) ⊆ rootWhole (interiorSlot i a)
  root_raw_large : ∀ i,
    rho * #(rootWhole (rootSlot i)) ≤ #(rootRaw (rootSlot i))
  interior_raw_large : ∀ i a,
    rho * #(rootWhole (interiorSlot i a)) ≤
      #(rootRaw (interiorSlot i a))
  direct_uniform : ∀ i, F.parent i = Sum.inl 0 →
    G.IsUniform rho sourceWhole (rootWhole (rootSlot i))
  direct_density : ∀ i, F.parent i = Sum.inl 0 →
    density ≤ G.edgeDensity sourceWhole (rootWhole (rootSlot i))
  attach_uniform : ∀ i j a, F.parent i = Sum.inr ⟨j, a⟩ →
    G.IsUniform rho
      (HierarchicalSegmentForest.rawCandidate F rootSlot rootWhole
        (fun i a ↦ rootWhole (interiorSlot i a)) j a)
      (rootWhole (rootSlot i))
  attach_density : ∀ i j a, F.parent i = Sum.inr ⟨j, a⟩ →
    density ≤ G.edgeDensity
      (HierarchicalSegmentForest.rawCandidate F rootSlot rootWhole
        (fun i a ↦ rootWhole (interiorSlot i a)) j a)
      (rootWhole (rootSlot i))
  internal_uniform : ∀ i a b, (F.segments.tree i).Adj a b →
    b ≠ F.segments.root i →
    G.IsUniform rho
      (HierarchicalSegmentForest.rawCandidate F rootSlot rootWhole
        (fun i a ↦ rootWhole (interiorSlot i a)) i a)
      (rootWhole (interiorSlot i b))
  internal_density : ∀ i a b, (F.segments.tree i).Adj a b →
    b ≠ F.segments.root i →
    density ≤ G.edgeDensity
      (HierarchicalSegmentForest.rawCandidate F rootSlot rootWhole
        (fun i a ↦ rootWhole (interiorSlot i a)) i a)
      (rootWhole (interiorSlot i b))
  pool_load : ∀ p,
    HierarchicalSegmentForest.poolLoad F
        (fun i ↦ slotPool (rootSlot i))
        (fun i ↦ slotPool (interiorSlot i (F.segments.root i))) p ≤
      poolCapacity p
  removal : ∀ i a,
    HierarchicalSegmentForest.coordinateRemovalBudget F rho rootSlot rootWhole
        (fun i a ↦ rootWhole (interiorSlot i a)) i a ≤
      removalBudget
  root_capacity : ∀ i,
    (poolCapacity (slotPool (rootSlot i)) + 1 : ℝ) + removalBudget + 1 ≤
      (density - rho) * #(rootRaw (rootSlot i))
  interior_capacity : ∀ i a,
    (poolCapacity (slotPool (interiorSlot i a)) + 1 : ℝ) +
        removalBudget + 1 ≤
      (density - rho) * #(rootRaw (interiorSlot i a))
  bad_budget :
    (#(Finset.univ.filter fun i ↦ F.parent i = Sum.inl 0) : ℝ) *
        (rho * #sourceWhole) < #sourceRaw
  root_raw_disjoint : ∀ i j,
    slotPool (rootSlot i) ≠ slotPool (rootSlot j) →
    Disjoint (rootRaw (rootSlot i)) (rootRaw (rootSlot j))
  interior_raw_disjoint : ∀ i a j b,
    slotPool (interiorSlot i a) ≠ slotPool (interiorSlot j b) →
    Disjoint (rootRaw (interiorSlot i a))
      (rootRaw (interiorSlot j b))
  root_interior_raw_disjoint : ∀ i j a,
    slotPool (rootSlot i) ≠ slotPool (interiorSlot j a) →
    Disjoint (rootRaw (rootSlot i)) (rootRaw (interiorSlot j a))

namespace TargetUnifiedHostFacts

/-- Realize the hierarchy from primitive regular-pair facts. -/
theorem exists_embedding
    {s : ℕ} {B RootSlot Pool : Type*}
    [Fintype B] [DecidableEq B] [DecidableEq Pool]
    (F : HierarchicalSegmentForest 1 s)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho density : ℝ)
    (sourceWhole sourceRaw : Finset B)
    (rootSlot : Fin s → RootSlot)
    (interiorSlot : (i : Fin s) → Fin (F.segments.size i) → RootSlot)
    (slotPool : RootSlot → Pool)
    (rootWhole rootRaw : RootSlot → Finset B)
    (poolCapacity : Pool → ℕ) (removalBudget : ℝ)
    (H : TargetUnifiedHostFacts F G rho density sourceWhole sourceRaw rootSlot
      interiorSlot slotPool rootWhole rootRaw poolCapacity removalBudget) :
    ∃ z ∈ sourceRaw,
      Nonempty (HierarchicalSegmentForest.HierarchicalCandidateEmbedding F G
        (fun _ ↦ z)
        (HierarchicalSegmentForest.targetRootCandidate F G rho rootSlot
          rootWhole rootRaw (fun i a ↦ rootWhole (interiorSlot i a))
          (fun i a ↦ rootRaw (interiorSlot i a)) {z})
        (HierarchicalSegmentForest.targetInteriorCandidate F G rho rootSlot
          rootWhole rootRaw (fun i a ↦ rootWhole (interiorSlot i a))
          (fun i a ↦ rootRaw (interiorSlot i a)) {z})) := by
  exact HierarchicalSegmentForest.exists_targetUnifiedHierarchyEmbedding
    F G rho density sourceWhole sourceRaw rootSlot interiorSlot slotPool
    rootWhole rootRaw poolCapacity removalBudget H.interior_pool
    H.source_subset H.source_large H.root_raw_subset H.interior_raw_subset
    H.root_raw_large H.interior_raw_large H.direct_uniform H.direct_density
    H.attach_uniform H.attach_density H.internal_uniform H.internal_density
    H.pool_load H.removal H.root_capacity H.interior_capacity H.bad_budget
    H.root_raw_disjoint H.interior_raw_disjoint H.root_interior_raw_disjoint

end TargetUnifiedHostFacts

/-- Prescribed-root version used in Lemma 6.15.  The exceptional matching
families are defined from the actual degree row of `originalRoot`, so the
root cannot be reselected after the source allocation. -/
structure PrescribedTargetUnifiedHostFacts
    {s : ℕ} {B RootSlot Pool : Type*}
    [Fintype B] [DecidableEq B] [DecidableEq Pool]
    (F : HierarchicalSegmentForest 1 s)
    (G : SimpleGraph B) [DecidableRel G.Adj] (rho : ℝ)
    (originalRoot : B)
    (rootSlot : Fin s → RootSlot)
    (interiorSlot : (i : Fin s) → Fin (F.segments.size i) → RootSlot)
    (slotPool : RootSlot → Pool)
    (rootWhole rootRaw : RootSlot → Finset B) where
  attach_original_capacity : ∀ i q, F.parent i = Sum.inl q →
    (HierarchicalSegmentForest.poolLoad F
        (fun i ↦ slotPool (rootSlot i))
        (fun i ↦ slotPool (interiorSlot i (F.segments.root i)))
        (slotPool (rootSlot i)) + 1 : ℝ) +
      #(HierarchicalSegmentForest.targetCoordinateRemoved F G rho rootSlot
          rootWhole rootRaw (fun i a ↦ rootWhole (interiorSlot i a))
          (fun i a ↦ rootRaw (interiorSlot i a)) i
          (F.segments.root i) ∪ {originalRoot}) ≤
        (#((rootRaw (rootSlot i)).filter (G.Adj originalRoot)) : ℝ)
  attach_capacity : ∀ i j a, F.parent i = Sum.inr ⟨j, a⟩ →
    (HierarchicalSegmentForest.poolLoad F
        (fun i ↦ slotPool (rootSlot i))
        (fun i ↦ slotPool (interiorSlot i (F.segments.root i)))
        (slotPool (rootSlot i)) + 1 : ℝ) +
      #(HierarchicalSegmentForest.targetCoordinateRemoved F G rho rootSlot
          rootWhole rootRaw (fun i a ↦ rootWhole (interiorSlot i a))
          (fun i a ↦ rootRaw (interiorSlot i a)) i
          (F.segments.root i) ∪ {originalRoot}) ≤
        (G.edgeDensity
          (HierarchicalSegmentForest.rawCandidate F rootSlot rootWhole
            (fun i a ↦ rootWhole (interiorSlot i a)) j a)
          (rootWhole (rootSlot i)) - rho) * #(rootRaw (rootSlot i))
  internal_capacity : ∀ i a b, (F.segments.tree i).Adj a b →
    b ≠ F.segments.root i →
    (HierarchicalSegmentForest.poolLoad F
        (fun i ↦ slotPool (rootSlot i))
        (fun i ↦ slotPool (interiorSlot i (F.segments.root i)))
        (slotPool (interiorSlot i (F.segments.root i))) + 1 : ℝ) +
      #(HierarchicalSegmentForest.targetInteriorRemoved F G rho rootSlot
          rootWhole rootRaw (fun i a ↦ rootWhole (interiorSlot i a))
          (fun i a ↦ rootRaw (interiorSlot i a)) {originalRoot} i b) ≤
        (G.edgeDensity
          (HierarchicalSegmentForest.rawCandidate F rootSlot rootWhole
            (fun i a ↦ rootWhole (interiorSlot i a)) i a)
          (rootWhole (interiorSlot i b)) - rho) *
            #(rootRaw (interiorSlot i b))
  root_raw_disjoint : ∀ i j,
    slotPool (rootSlot i) ≠ slotPool (rootSlot j) →
    Disjoint (rootRaw (rootSlot i)) (rootRaw (rootSlot j))
  interior_raw_disjoint : ∀ i a j b,
    slotPool (interiorSlot i (F.segments.root i)) ≠
        slotPool (interiorSlot j (F.segments.root j)) →
    Disjoint (rootRaw (interiorSlot i a))
      (rootRaw (interiorSlot j b))
  root_interior_raw_disjoint : ∀ i j a,
    slotPool (rootSlot i) ≠
        slotPool (interiorSlot j (F.segments.root j)) →
    Disjoint (rootRaw (rootSlot i)) (rootRaw (interiorSlot j a))

namespace PrescribedTargetUnifiedHostFacts

theorem exists_embedding
    {s : ℕ} {B RootSlot Pool : Type*}
    [Fintype B] [DecidableEq B] [DecidableEq Pool]
    (F : HierarchicalSegmentForest 1 s)
    (G : SimpleGraph B) [DecidableRel G.Adj] (rho : ℝ)
    (originalRoot : B)
    (rootSlot : Fin s → RootSlot)
    (interiorSlot : (i : Fin s) → Fin (F.segments.size i) → RootSlot)
    (slotPool : RootSlot → Pool)
    (rootWhole rootRaw : RootSlot → Finset B)
    (H : PrescribedTargetUnifiedHostFacts F G rho originalRoot rootSlot
      interiorSlot slotPool rootWhole rootRaw) :
    Nonempty (HierarchicalSegmentForest.HierarchicalCandidateEmbedding F G
      (fun _ ↦ originalRoot)
      (HierarchicalSegmentForest.targetRootCandidate F G rho rootSlot
        rootWhole rootRaw (fun i a ↦ rootWhole (interiorSlot i a))
        (fun i a ↦ rootRaw (interiorSlot i a)) {originalRoot})
      (HierarchicalSegmentForest.targetInteriorCandidate F G rho rootSlot
        rootWhole rootRaw (fun i a ↦ rootWhole (interiorSlot i a))
        (fun i a ↦ rootRaw (interiorSlot i a)) {originalRoot})) := by
  let rootPool : Fin s → Pool := fun i ↦ slotPool (rootSlot i)
  let interiorPool : Fin s → Pool := fun i ↦
    slotPool (interiorSlot i (F.segments.root i))
  let interiorWhole : (i : Fin s) → Fin (F.segments.size i) → Finset B :=
    fun i a ↦ rootWhole (interiorSlot i a)
  let interiorRaw : (i : Fin s) → Fin (F.segments.size i) → Finset B :=
    fun i a ↦ rootRaw (interiorSlot i a)
  let system := HierarchicalSegmentForest.targetUnifiedCleanedRegularSystem
    F G rho (fun _ ↦ originalRoot) rootSlot rootPool interiorPool rootWhole
    rootRaw interiorWhole interiorRaw {originalRoot}
    (by
      intro z hz
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hz
      simp)
    H.attach_original_capacity H.attach_capacity H.internal_capacity
    (by intro q q' _; exact Subsingleton.elim q q')
    H.root_raw_disjoint H.interior_raw_disjoint
    H.root_interior_raw_disjoint
  exact HierarchicalSegmentForest.exists_hierarchicalUnifiedRegularEmbedding
    F G (fun _ ↦ originalRoot) rootPool interiorPool
    (HierarchicalSegmentForest.targetRootCandidate F G rho rootSlot
      rootWhole rootRaw interiorWhole interiorRaw {originalRoot})
    (HierarchicalSegmentForest.targetInteriorCandidate F G rho rootSlot
      rootWhole rootRaw interiorWhole interiorRaw {originalRoot}) system

end PrescribedTargetUnifiedHostFacts

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {B : Type v} [Fintype B] [DecidableEq B]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

/-- The concrete no-`C` Claim-6.15 hierarchy, realized all the way back to
a copy of the literal input tree. -/
theorem isContained_of_noCHostFacts
    (hT : T.IsTree) (P : Erdos547b.TreePartition.ZhaoForestPartition
      T globalRoot small) (optional : Finset V)
    {available : Finset (BranchIndex P)} {target slack : ℕ}
    (S : SelectedF0 P available target slack)
    {K0 K1 Kb Edge : Type*}
    [Fintype K0] [DecidableEq K0]
    [Fintype K1] [DecidableEq K1]
    [Fintype Kb] [DecidableEq Kb]
    [DecidableEq Edge]
    (capacity0 : K0 → ℕ) (capacity1 : K1 → ℕ)
    (capacityb : Kb → ℕ)
    (A : SourceAllocation P S K0 K1 Kb capacity0 capacity1 capacityb)
    (edge0 : K0 → Edge) (edge1 : K1 → Edge) (edgeb : Kb → Edge)
    (rootSide0 : K0 → Fin 2) (rootSide1 : K1 → Fin 2)
    (rootSideb : Kb → Fin 2)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ) (originalRoot : B)
    (rootWhole rootRaw : RootSlot Edge → Finset B)
    (H : PrescribedTargetUnifiedHostFacts
      (AllocationHierarchy hT P optional) G rho originalRoot
      (hierarchyRootSlot hT P optional S capacity0 capacity1 capacityb A
        edge0 edge1 edgeb rootSide0 rootSide1 rootSideb)
      (hierarchyInteriorSlot hT P optional S capacity0 capacity1 capacityb A
        edge0 edge1 edgeb rootSide0 rootSide1 rootSideb)
      rootSlotPool rootWhole rootRaw) :
    T.IsContained G := by
  let F := AllocationHierarchy hT P optional
  let rslot := hierarchyRootSlot hT P optional S capacity0 capacity1 capacityb
    A edge0 edge1 edgeb rootSide0 rootSide1 rootSideb
  let islot := hierarchyInteriorSlot hT P optional S capacity0 capacity1
    capacityb A edge0 edge1 edgeb rootSide0 rootSide1 rootSideb
  obtain ⟨E⟩ := H.exists_embedding F G rho originalRoot rslot islot
    rootSlotPool rootWhole rootRaw
  let rootCandidate := HierarchicalSegmentForest.targetRootCandidate F G rho
    rslot rootWhole rootRaw (fun i a ↦ rootWhole (islot i a))
      (fun i a ↦ rootRaw (islot i a)) {originalRoot}
  let interiorCandidate :=
    HierarchicalSegmentForest.targetInteriorCandidate F G rho rslot rootWhole
      rootRaw (fun i a ↦ rootWhole (islot i a))
        (fun i a ↦ rootRaw (islot i a)) {originalRoot}
  let Efull := fullTreeRegularEmbeddingOfHierarchyEmbedding T hT globalRoot
    (AllocationSpecial hT P optional) G (fun _ ↦ originalRoot) rootCandidate
      interiorCandidate E
  exact Efull.fullCopy.isContained

/-- Endpoint-side-exact Claim-6.15 realization.  Every non-global literal
source vertex is its own segment, the collision pool is the oriented root
slot itself, and only `distinguished` source vertices are redirected to an
A/B reserve.  Consequently the host capacity attached to `(e, side)` is
charged by precisely the vertices placed on that endpoint, rather than by
the total mass of the branches assigned to `e`. -/
theorem isContained_of_allVertexNoCHostFacts
    (hT : T.IsTree) (P : Erdos547b.TreePartition.ZhaoForestPartition
      T globalRoot small) (distinguished : Finset V)
    {available : Finset (BranchIndex P)} {target slack : ℕ}
    (S : SelectedF0 P available target slack)
    {K0 K1 Kb Edge : Type*}
    [Fintype K0] [DecidableEq K0]
    [Fintype K1] [DecidableEq K1]
    [Fintype Kb] [DecidableEq Kb]
    [DecidableEq Edge]
    (capacity0 : K0 → ℕ) (capacity1 : K1 → ℕ)
    (capacityb : Kb → ℕ)
    (A : SourceAllocation P S K0 K1 Kb capacity0 capacity1 capacityb)
    (edge0 : K0 → Edge) (edge1 : K1 → Edge) (edgeb : Kb → Edge)
    (rootSide0 : K0 → Fin 2) (rootSide1 : K1 → Fin 2)
    (rootSideb : Kb → Fin 2)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ) (originalRoot : B)
    (rootWhole rootRaw : RootSlot Edge → Finset B)
    (H : PrescribedTargetUnifiedHostFacts
      (AllocationHierarchy hT P Finset.univ) G rho originalRoot
      (allVertexRootSlot hT P S capacity0 capacity1 capacityb A edge0 edge1
        edgeb rootSide0 rootSide1 rootSideb distinguished)
      (allVertexInteriorSlot hT P S capacity0 capacity1 capacityb A edge0
        edge1 edgeb rootSide0 rootSide1 rootSideb distinguished)
      (id : RootSlot Edge → RootSlot Edge) rootWhole rootRaw) :
    T.IsContained G := by
  let F := AllocationHierarchy hT P Finset.univ
  let rslot := allVertexRootSlot hT P S capacity0 capacity1 capacityb A edge0
    edge1 edgeb rootSide0 rootSide1 rootSideb distinguished
  let islot := allVertexInteriorSlot hT P S capacity0 capacity1 capacityb A
    edge0 edge1 edgeb rootSide0 rootSide1 rootSideb distinguished
  obtain ⟨E⟩ := H.exists_embedding F G rho originalRoot rslot islot id
    rootWhole rootRaw
  let rootCandidate := HierarchicalSegmentForest.targetRootCandidate F G rho
    rslot rootWhole rootRaw (fun i a ↦ rootWhole (islot i a))
      (fun i a ↦ rootRaw (islot i a)) {originalRoot}
  let interiorCandidate :=
    HierarchicalSegmentForest.targetInteriorCandidate F G rho rslot rootWhole
      rootRaw (fun i a ↦ rootWhole (islot i a))
        (fun i a ↦ rootRaw (islot i a)) {originalRoot}
  let Efull := fullTreeRegularEmbeddingOfHierarchyEmbedding T hT globalRoot
    (AllocationSpecial hT P Finset.univ) G (fun _ ↦ originalRoot)
      rootCandidate interiorCandidate E
  exact Efull.fullCopy.isContained

end Erdos547b.ZhaoClaim615HierarchicalEmbedding

#print axioms Erdos547b.ZhaoClaim615HierarchicalEmbedding.isContained_of_noCHostFacts
#print axioms Erdos547b.ZhaoClaim615HierarchicalEmbedding.isContained_of_allVertexNoCHostFacts
