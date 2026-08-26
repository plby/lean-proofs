/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.HierarchicalTargetCoordinateApplication
import ErdosProblems.Erdos547b.Lemma614HierarchicalUnifiedFullTree
import ErdosProblems.Erdos547b.Claim616HierarchyClassification

/-!
# Generic containment from a coordinate-sensitive hierarchy

This file isolates the layout-independent endpoint of the coordinate online
backend.  Its host certificate contains only literal reservoir, regular-pair,
removal, capacity, and separation facts.  The physical-pool capacity is fixed
definitionally to the exact coordinate load, and the resulting hierarchy copy
is transported back to the original tree.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoHierarchicalCoordinateContainment

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoLemma59Hierarchical
open Erdos547b.ZhaoLemma59HierarchicalRegular
open Erdos547b.ZhaoLemma59HierarchicalCoordinatePools
open Erdos547b.ZhaoLemma59HierarchicalTargetCleaning
open Erdos547b.ZhaoLemma59HierarchicalTargetCoordinateApplication
open Erdos547b.ZhaoLemma614HierarchicalFullTree
open Erdos547b.ZhaoLemma614HierarchicalUnifiedFullTree
open Erdos547b.ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalTargetCleaning.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalCoordinatePools.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalTargetUnifiedApplication.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalTargetCoordinateApplication.HierarchicalSegmentForest

universe u v w

/-- Primitive facts sufficient for the endpoint-sensitive online hierarchy.
The load occurring in both capacity fields is the literal load of that exact
root/interior coordinate slot. -/
structure CoordinateHierarchyHostFacts
    {s small : ℕ} {Host : Type v} {RootSlot : Type w}
    [Fintype Host] [DecidableEq Host] [DecidableEq RootSlot]
    (F : HierarchicalSegmentForest 1 s)
    (G : SimpleGraph Host) [DecidableRel G.Adj]
    (rho density : ℝ)
    (sourceWhole sourceRaw : Finset Host)
    (rootSlot : Fin s → RootSlot)
    (interiorSlot : (i : Fin s) → Fin (F.segments.size i) → RootSlot)
    (rootWhole rootRaw : RootSlot → Finset Host)
    (removalBudget : ℝ) : Prop where
  segment_small : ∀ i, F.segments.size i ≤ small
  source_subset : sourceRaw ⊆ sourceWhole
  source_large : rho * #sourceWhole ≤ #sourceRaw
  root_raw_subset : ∀ i, rootRaw (rootSlot i) ⊆ rootWhole (rootSlot i)
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
  removal : ∀ i a,
    coordinateRemovalBudget F rho rootSlot rootWhole
      (fun i a ↦ rootWhole (interiorSlot i a)) i a ≤ removalBudget
  root_capacity : ∀ i,
    (coordinatePoolLoad F rootSlot interiorSlot (rootSlot i) + small + 1 : ℝ) +
        removalBudget + 1 ≤
      (density - rho) * #(rootRaw (rootSlot i))
  interior_capacity : ∀ i a,
    (coordinatePoolLoad F rootSlot interiorSlot (interiorSlot i a) +
        small + 1 : ℝ) + removalBudget + 1 ≤
      (density - rho) * #(rootRaw (interiorSlot i a))
  bad_budget :
    (#(Finset.univ.filter fun i ↦ F.parent i = Sum.inl 0) : ℝ) *
        (rho * #sourceWhole) < #sourceRaw
  root_raw_disjoint : ∀ i j, rootSlot i ≠ rootSlot j →
    Disjoint (rootRaw (rootSlot i)) (rootRaw (rootSlot j))
  interior_raw_disjoint : ∀ i a j b,
    interiorSlot i a ≠ interiorSlot j b →
    Disjoint (rootRaw (interiorSlot i a)) (rootRaw (interiorSlot j b))
  root_interior_raw_disjoint : ∀ i j a,
    rootSlot i ≠ interiorSlot j a →
    Disjoint (rootRaw (rootSlot i)) (rootRaw (interiorSlot j a))

/-- The six regular-pair obligations, packaged independently of all numeric
capacity calculations. -/
structure CoordinateHierarchyPairFacts
    {s : ℕ} {Host : Type v} {RootSlot : Type w}
    [Fintype Host] [DecidableEq Host]
    (F : HierarchicalSegmentForest 1 s)
    (G : SimpleGraph Host) [DecidableRel G.Adj]
    (rho density : ℝ) (sourceWhole : Finset Host)
    (rootSlot : Fin s → RootSlot)
    (rootWhole : RootSlot → Finset Host)
    (interiorSlot : (i : Fin s) → Fin (F.segments.size i) → RootSlot) : Prop where
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

/-- Numeric and cardinality obligations, packaged independently of pair
classification and raw-reservoir separation. -/
structure CoordinateHierarchyCapacityFacts
    {s small : ℕ} {Host : Type v} {RootSlot : Type w}
    [Fintype Host] [DecidableEq Host] [DecidableEq RootSlot]
    (F : HierarchicalSegmentForest 1 s)
    (rho density : ℝ)
    (sourceWhole sourceRaw : Finset Host)
    (rootSlot : Fin s → RootSlot)
    (interiorSlot : (i : Fin s) → Fin (F.segments.size i) → RootSlot)
    (rootWhole rootRaw : RootSlot → Finset Host)
    (removalBudget : ℝ) : Prop where
  segment_small : ∀ i, F.segments.size i ≤ small
  source_large : rho * #sourceWhole ≤ #sourceRaw
  root_raw_large : ∀ i,
    rho * #(rootWhole (rootSlot i)) ≤ #(rootRaw (rootSlot i))
  interior_raw_large : ∀ i a,
    rho * #(rootWhole (interiorSlot i a)) ≤
      #(rootRaw (interiorSlot i a))
  removal : ∀ i a,
    coordinateRemovalBudget F rho rootSlot rootWhole
      (fun i a ↦ rootWhole (interiorSlot i a)) i a ≤ removalBudget
  root_capacity : ∀ i,
    (coordinatePoolLoad F rootSlot interiorSlot (rootSlot i) + small + 1 : ℝ) +
        removalBudget + 1 ≤
      (density - rho) * #(rootRaw (rootSlot i))
  interior_capacity : ∀ i a,
    (coordinatePoolLoad F rootSlot interiorSlot (interiorSlot i a) +
        small + 1 : ℝ) + removalBudget + 1 ≤
      (density - rho) * #(rootRaw (interiorSlot i a))
  bad_budget :
    (#(Finset.univ.filter fun i ↦ F.parent i = Sum.inl 0) : ℝ) *
        (rho * #sourceWhole) < #sourceRaw

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

/-- A literal realization of the canonical whole-tree hierarchy is a copy of
the original tree.  No copy, continuation, or containment statement is an
input. -/
theorem isContained_of_coordinateHierarchyHostFacts
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    {Host : Type v} [Fintype Host] [DecidableEq Host]
    {RootSlot : Type w} [DecidableEq RootSlot]
    (G : SimpleGraph Host) [DecidableRel G.Adj]
    (rho density : ℝ)
    (sourceWhole sourceRaw : Finset Host)
    (rootSlot : SegmentIndex hT P optional → RootSlot)
    (interiorSlot : (i : SegmentIndex hT P optional) →
      Fin ((AllocationHierarchy hT P optional).segments.size i) → RootSlot)
    (rootWhole rootRaw : RootSlot → Finset Host)
    (removalBudget : ℝ)
    (H : CoordinateHierarchyHostFacts (small := small)
      (AllocationHierarchy hT P optional) G
      rho density sourceWhole sourceRaw rootSlot interiorSlot rootWhole rootRaw
      removalBudget) :
    T.IsContained G := by
  let F := AllocationHierarchy hT P optional
  let poolCapacity : RootSlot → ℕ :=
    coordinatePoolLoad F rootSlot interiorSlot
  obtain ⟨z, hz, E⟩ := exists_targetCoordinateHierarchyEmbedding F G rho
    density small sourceWhole sourceRaw rootSlot interiorSlot id rootWhole
    rootRaw poolCapacity removalBudget H.segment_small H.source_subset
    H.source_large H.root_raw_subset H.interior_raw_subset H.root_raw_large
    H.interior_raw_large H.direct_uniform H.direct_density H.attach_uniform
    H.attach_density H.internal_uniform H.internal_density
    (by intro p; exact le_rfl) H.removal H.root_capacity
    H.interior_capacity H.bad_budget H.root_raw_disjoint
    H.interior_raw_disjoint H.root_interior_raw_disjoint
  let rootCandidate := targetRootCandidate F G rho rootSlot rootWhole rootRaw
    (fun i a ↦ rootWhole (interiorSlot i a))
    (fun i a ↦ rootRaw (interiorSlot i a)) {z}
  let interiorCandidate := targetInteriorCandidate F G rho rootSlot rootWhole
    rootRaw (fun i a ↦ rootWhole (interiorSlot i a))
    (fun i a ↦ rootRaw (interiorSlot i a)) {z}
  obtain ⟨E⟩ := E
  let Efull := fullTreeRegularEmbeddingOfHierarchyEmbedding T hT globalRoot
    (AllocationSpecial hT P optional) G (fun _ ↦ z) rootCandidate
    interiorCandidate E
  exact Efull.fullCopy.isContained

end Erdos547b.ZhaoHierarchicalCoordinateContainment

#print axioms Erdos547b.ZhaoHierarchicalCoordinateContainment.isContained_of_coordinateHierarchyHostFacts
