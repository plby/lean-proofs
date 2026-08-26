/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616HierarchicalCoordinateSourceLayout
import ErdosProblems.Erdos547b.HierarchicalTargetCoordinateApplication
import ErdosProblems.Erdos547b.Lemma614HierarchicalUnifiedFullTree

/-!
# Cut-aware coordinate realization for Claim 6.16

This is the source-specialized endpoint of the coordinate online backend.
The capacity of a physical endpoint is definitionally its exact hierarchy
coordinate load; callers must prove the genuine residual regular-pair margin
for that load.  In particular, no aggregate source degree is treated as a
pointwise endpoint capacity.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim616HierarchicalCoordinateEmbedding

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim68ParityHalf
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616HierarchicalAllocation
open Erdos547b.ZhaoClaim616HierarchicalSourceLayout
open Erdos547b.ZhaoClaim616HierarchicalCoordinateSourceLayout
open Erdos547b.ZhaoLemma59Hierarchical
open Erdos547b.ZhaoLemma59HierarchicalOnline
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

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small target slack : ℕ}

section

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

abbrev coordinateRootSlot :=
  coordinateHierarchyRootSlot hT P optional S clusterCapacity allowed0
    capacity1 capacityb base0 A edge1 edgeb orient

abbrev coordinateInteriorSlot :=
  coordinateHierarchyInteriorSlot hT P optional S clusterCapacity allowed0
    capacity1 capacityb base0 A edge0 edge1 edgeb orient

abbrev exactCoordinateCapacity (p : RootSlot CIndex Edge) : ℕ :=
  coordinatePoolLoad (AllocationHierarchy hT P optional)
    (coordinateRootSlot hT P optional S clusterCapacity allowed0 capacity1
      capacityb base0 A edge1 edgeb orient)
    (coordinateInteriorSlot hT P optional S clusterCapacity allowed0 capacity1
      capacityb base0 A edge0 edge1 edgeb orient) p

/-- A literal coordinate realization of the cut-aware hierarchy gives a copy
of the original tree.  The hypotheses are only host pair, raw-reservoir, and
numeric capacity facts; the theorem takes no copy, continuation, or cleaned
system premise. -/
theorem isContained_of_coordinateHostFacts
    {B : Type v} [Fintype B] [DecidableEq B]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho density : ℝ)
    (sourceWhole sourceRaw : Finset B)
    (rootWhole rootRaw : RootSlot CIndex Edge → Finset B)
    (removalBudget : ℝ)
    (hsegmentSmall : ∀ i,
      (AllocationHierarchy hT P optional).segments.size i ≤ small)
    (hsourceSubset : sourceRaw ⊆ sourceWhole)
    (hsourceLarge : rho * #sourceWhole ≤ #sourceRaw)
    (hrootRawSubset : ∀ i,
      rootRaw (coordinateRootSlot hT P optional S clusterCapacity allowed0
        capacity1 capacityb base0 A edge1 edgeb orient i) ⊆
      rootWhole (coordinateRootSlot hT P optional S clusterCapacity allowed0
        capacity1 capacityb base0 A edge1 edgeb orient i))
    (hinteriorRawSubset : ∀ i a,
      rootRaw (coordinateInteriorSlot hT P optional S clusterCapacity allowed0
        capacity1 capacityb base0 A edge0 edge1 edgeb orient i a) ⊆
      rootWhole (coordinateInteriorSlot hT P optional S clusterCapacity
        allowed0 capacity1 capacityb base0 A edge0 edge1 edgeb orient i a))
    (hrootRawLarge : ∀ i,
      rho * #(rootWhole (coordinateRootSlot hT P optional S clusterCapacity
        allowed0 capacity1 capacityb base0 A edge1 edgeb orient i)) ≤
      #(rootRaw (coordinateRootSlot hT P optional S clusterCapacity allowed0
        capacity1 capacityb base0 A edge1 edgeb orient i)))
    (hinteriorRawLarge : ∀ i a,
      rho * #(rootWhole (coordinateInteriorSlot hT P optional S
        clusterCapacity allowed0 capacity1 capacityb base0 A edge0 edge1
        edgeb orient i a)) ≤
      #(rootRaw (coordinateInteriorSlot hT P optional S clusterCapacity
        allowed0 capacity1 capacityb base0 A edge0 edge1 edgeb orient i a)))
    (hdirectUniform : ∀ i,
      (AllocationHierarchy hT P optional).parent i = Sum.inl 0 →
      G.IsUniform rho sourceWhole
        (rootWhole (coordinateRootSlot hT P optional S clusterCapacity
          allowed0 capacity1 capacityb base0 A edge1 edgeb orient i)))
    (hdirectDensity : ∀ i,
      (AllocationHierarchy hT P optional).parent i = Sum.inl 0 →
      density ≤ G.edgeDensity sourceWhole
        (rootWhole (coordinateRootSlot hT P optional S clusterCapacity
          allowed0 capacity1 capacityb base0 A edge1 edgeb orient i)))
    (hattachUniform : ∀ i j a,
      (AllocationHierarchy hT P optional).parent i = Sum.inr ⟨j, a⟩ →
      G.IsUniform rho
        (Erdos547b.ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
          (AllocationHierarchy hT P optional)
          (coordinateRootSlot hT P optional S clusterCapacity allowed0
            capacity1 capacityb base0 A edge1 edgeb orient) rootWhole
          (fun i a ↦ rootWhole
            (coordinateInteriorSlot hT P optional S clusterCapacity allowed0
              capacity1 capacityb base0 A edge0 edge1 edgeb orient i a)) j a)
        (rootWhole (coordinateRootSlot hT P optional S clusterCapacity
          allowed0 capacity1 capacityb base0 A edge1 edgeb orient i)))
    (hattachDensity : ∀ i j a,
      (AllocationHierarchy hT P optional).parent i = Sum.inr ⟨j, a⟩ →
      density ≤ G.edgeDensity
        (Erdos547b.ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
          (AllocationHierarchy hT P optional)
          (coordinateRootSlot hT P optional S clusterCapacity allowed0
            capacity1 capacityb base0 A edge1 edgeb orient) rootWhole
          (fun i a ↦ rootWhole
            (coordinateInteriorSlot hT P optional S clusterCapacity allowed0
              capacity1 capacityb base0 A edge0 edge1 edgeb orient i a)) j a)
        (rootWhole (coordinateRootSlot hT P optional S clusterCapacity
          allowed0 capacity1 capacityb base0 A edge1 edgeb orient i)))
    (hinternalUniform : ∀ i a b,
      ((AllocationHierarchy hT P optional).segments.tree i).Adj a b →
      b ≠ (AllocationHierarchy hT P optional).segments.root i →
      G.IsUniform rho
        (Erdos547b.ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
          (AllocationHierarchy hT P optional)
          (coordinateRootSlot hT P optional S clusterCapacity allowed0
            capacity1 capacityb base0 A edge1 edgeb orient) rootWhole
          (fun i a ↦ rootWhole
            (coordinateInteriorSlot hT P optional S clusterCapacity allowed0
              capacity1 capacityb base0 A edge0 edge1 edgeb orient i a)) i a)
        (rootWhole (coordinateInteriorSlot hT P optional S clusterCapacity
          allowed0 capacity1 capacityb base0 A edge0 edge1 edgeb orient i b)))
    (hinternalDensity : ∀ i a b,
      ((AllocationHierarchy hT P optional).segments.tree i).Adj a b →
      b ≠ (AllocationHierarchy hT P optional).segments.root i →
      density ≤ G.edgeDensity
        (Erdos547b.ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
          (AllocationHierarchy hT P optional)
          (coordinateRootSlot hT P optional S clusterCapacity allowed0
            capacity1 capacityb base0 A edge1 edgeb orient) rootWhole
          (fun i a ↦ rootWhole
            (coordinateInteriorSlot hT P optional S clusterCapacity allowed0
              capacity1 capacityb base0 A edge0 edge1 edgeb orient i a)) i a)
        (rootWhole (coordinateInteriorSlot hT P optional S clusterCapacity
          allowed0 capacity1 capacityb base0 A edge0 edge1 edgeb orient i b)))
    (hremoval : ∀ i a,
      coordinateRemovalBudget (AllocationHierarchy hT P optional) rho
        (coordinateRootSlot hT P optional S clusterCapacity allowed0
          capacity1 capacityb base0 A edge1 edgeb orient) rootWhole
        (fun i a ↦ rootWhole
          (coordinateInteriorSlot hT P optional S clusterCapacity allowed0
            capacity1 capacityb base0 A edge0 edge1 edgeb orient i a)) i a ≤
        removalBudget)
    (hrootCapacity : ∀ i,
      (exactCoordinateCapacity hT P optional S clusterCapacity allowed0
          capacity1 capacityb base0 A edge0 edge1 edgeb orient
          (coordinateRootSlot hT P optional S clusterCapacity allowed0
            capacity1 capacityb base0 A edge1 edgeb orient i) + small + 1 : ℝ) +
          removalBudget + 1 ≤
        (density - rho) *
          #(rootRaw (coordinateRootSlot hT P optional S clusterCapacity
            allowed0 capacity1 capacityb base0 A edge1 edgeb orient i)))
    (hinteriorCapacity : ∀ i a,
      (exactCoordinateCapacity hT P optional S clusterCapacity allowed0
          capacity1 capacityb base0 A edge0 edge1 edgeb orient
          (coordinateInteriorSlot hT P optional S clusterCapacity allowed0
            capacity1 capacityb base0 A edge0 edge1 edgeb orient i a) +
          small + 1 : ℝ) + removalBudget + 1 ≤
        (density - rho) *
          #(rootRaw (coordinateInteriorSlot hT P optional S clusterCapacity
            allowed0 capacity1 capacityb base0 A edge0 edge1 edgeb orient i a)))
    (hbadBudget :
      (#(Finset.univ.filter fun i ↦
          (AllocationHierarchy hT P optional).parent i = Sum.inl 0) : ℝ) *
        (rho * #sourceWhole) < #sourceRaw)
    (hrootRawDisjoint : ∀ i j,
      coordinateRootSlot hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge1 edgeb orient i ≠
        coordinateRootSlot hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge1 edgeb orient j →
      Disjoint
        (rootRaw (coordinateRootSlot hT P optional S clusterCapacity allowed0
          capacity1 capacityb base0 A edge1 edgeb orient i))
        (rootRaw (coordinateRootSlot hT P optional S clusterCapacity allowed0
          capacity1 capacityb base0 A edge1 edgeb orient j)))
    (hinteriorRawDisjoint : ∀ i a j b,
      coordinateInteriorSlot hT P optional S clusterCapacity allowed0
          capacity1 capacityb base0 A edge0 edge1 edgeb orient i a ≠
        coordinateInteriorSlot hT P optional S clusterCapacity allowed0
          capacity1 capacityb base0 A edge0 edge1 edgeb orient j b →
      Disjoint
        (rootRaw (coordinateInteriorSlot hT P optional S clusterCapacity
          allowed0 capacity1 capacityb base0 A edge0 edge1 edgeb orient i a))
        (rootRaw (coordinateInteriorSlot hT P optional S clusterCapacity
          allowed0 capacity1 capacityb base0 A edge0 edge1 edgeb orient j b)))
    (hrootInteriorRawDisjoint : ∀ i j a,
      coordinateRootSlot hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge1 edgeb orient i ≠
        coordinateInteriorSlot hT P optional S clusterCapacity allowed0
          capacity1 capacityb base0 A edge0 edge1 edgeb orient j a →
      Disjoint
        (rootRaw (coordinateRootSlot hT P optional S clusterCapacity allowed0
          capacity1 capacityb base0 A edge1 edgeb orient i))
        (rootRaw (coordinateInteriorSlot hT P optional S clusterCapacity
          allowed0 capacity1 capacityb base0 A edge0 edge1 edgeb orient j a))) :
    T.IsContained G := by
  let F := AllocationHierarchy hT P optional
  let rslot := coordinateRootSlot hT P optional S clusterCapacity allowed0
    capacity1 capacityb base0 A edge1 edgeb orient
  let islot := coordinateInteriorSlot hT P optional S clusterCapacity allowed0
    capacity1 capacityb base0 A edge0 edge1 edgeb orient
  let poolCapacity := exactCoordinateCapacity hT P optional S clusterCapacity
    allowed0 capacity1 capacityb base0 A edge0 edge1 edgeb orient
  obtain ⟨z, hz, E⟩ := exists_targetCoordinateHierarchyEmbedding F G rho
    density small sourceWhole sourceRaw rslot islot id rootWhole rootRaw
      poolCapacity removalBudget hsegmentSmall hsourceSubset hsourceLarge
      hrootRawSubset hinteriorRawSubset hrootRawLarge hinteriorRawLarge
      hdirectUniform hdirectDensity hattachUniform hattachDensity
      hinternalUniform hinternalDensity (by intro p; exact le_rfl) hremoval
      hrootCapacity hinteriorCapacity hbadBudget hrootRawDisjoint
      hinteriorRawDisjoint hrootInteriorRawDisjoint
  let rootCandidate := targetRootCandidate F G rho rslot rootWhole rootRaw
    (fun i a ↦ rootWhole (islot i a)) (fun i a ↦ rootRaw (islot i a)) {z}
  let interiorCandidate := targetInteriorCandidate F G rho rslot rootWhole
    rootRaw (fun i a ↦ rootWhole (islot i a))
      (fun i a ↦ rootRaw (islot i a)) {z}
  obtain ⟨E⟩ := E
  let Efull := fullTreeRegularEmbeddingOfHierarchyEmbedding T hT globalRoot
    (AllocationSpecial hT P optional) G (fun _ ↦ z) rootCandidate
      interiorCandidate E
  exact Efull.fullCopy.isContained

end

end Erdos547b.ZhaoClaim616HierarchicalCoordinateEmbedding

#print axioms Erdos547b.ZhaoClaim616HierarchicalCoordinateEmbedding.isContained_of_coordinateHostFacts
