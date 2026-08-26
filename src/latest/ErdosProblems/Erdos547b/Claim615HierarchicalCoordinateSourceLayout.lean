/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615CoordinateSourceAllocation
import ErdosProblems.Erdos547b.Claim616HierarchyAttachments
import ErdosProblems.Erdos547b.HierarchicalCoordinatePools

/-!
# Coordinate-sensitive source layout for Zhao Claim 6.15

The orientation supplied by Lemma 5.4 may vary from branch to branch even
when several branches share one matching edge.  This layout therefore keeps
the literal endpoint of every hierarchy coordinate.  Component roots and
the explicitly distinguished cut parents stay in the two A/B reservoirs;
all other branch coordinates use their assigned matching edge and their
branch-specific orientation.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim615HierarchicalCoordinateSourceLayout

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68ParityHalf
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim615CoordinateSourceAllocation

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

/-- The distinguished reservoir prescribed by the literal parity of a
source vertex.  This modern coordinate layout keeps the definition locally
so it does not depend on the older coarse-pool Claim 6.15 module. -/
def sourceVertexReservoirSide
    (P : ZhaoForestPartition T globalRoot small) (x : V) : Fin 2 :=
  if T.dist globalRoot x % 2 = (majorParity P).val then 0 else 1

@[simp] theorem sourceVertexReservoirSide_root
    (P : ZhaoForestPartition T globalRoot small) (q : Fin P.numParts) :
    sourceVertexReservoirSide P (P.roots q) = componentReservoirSide P q := by
  simp [sourceVertexReservoirSide, componentReservoirSide]

theorem sourceVertexReservoirSide_ne_of_adj
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    {x y : V} (hxy : T.Adj x y) :
    sourceVertexReservoirSide P x ≠ sourceVertexReservoirSide P y := by
  have hparity := TreePartition.rootParity_ne_of_adj hT globalRoot hxy
  have hxlt : T.dist globalRoot x % 2 < 2 := Nat.mod_lt _ (by omega)
  have hylt : T.dist globalRoot y % 2 < 2 := Nat.mod_lt _ (by omega)
  have hmlt : (majorParity P).val < 2 := (majorParity P).isLt
  simp only [sourceVertexReservoirSide]
  split <;> split <;> simp_all <;> omega

section Allocated

variable
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional distinguished : Finset V)
    (distinguishedSide : V → Fin 2)
    {available : Finset (BranchIndex P)} {target slack : ℕ}
    (S : ZhaoClaim615SourceSelection.SelectedF0 P available target slack)
    {K0 K1 Kb Edge : Type*}
    [Fintype K0] [DecidableEq K0]
    [Fintype K1] [DecidableEq K1]
    [Fintype Kb] [DecidableEq Kb]
    [DecidableEq Edge]
    (capacity0 : K0 → ℕ) (capacity1 : K1 → ℕ)
    (capacityb : Kb → ℕ)
    (A : SourceAllocation P S K0 K1 Kb capacity0 capacity1 capacityb)
    (edge0 : K0 → Edge) (edge1 : K1 → Edge) (edgeb : Kb → Edge)
    (orient : BranchIndex P → Fin 2 ≃ Fin 2)

/-- Literal physical matching edge assigned to a canonical branch. -/
def coordinateBranchEdge (j : BranchIndex P) : Edge :=
  if _hj0 : j ∈ S.selected then edge0 (A.F0edge j)
  else if _hj1 : j ∈ majorResidualBranches P S then edge1 (A.F1edge j)
  else edgeb (A.Fbedge j)

/-- Literal matching endpoint occupied by one coordinate of a branch. -/
def coordinateBranchSlot (j : BranchIndex P) (side : Fin 2) : RootSlot Edge :=
  Sum.inr ⟨coordinateBranchEdge P S capacity0 capacity1 capacityb A
    edge0 edge1 edgeb j, orient j side⟩

/-- Root slot of one hierarchy segment.  Only explicitly distinguished
source vertices are redirected to A/B. -/
def coordinateHierarchyRootSlot
    (i : SegmentIndex hT P optional) : RootSlot Edge :=
  if SegmentRootOriginal hT P optional i ∈ distinguished then
    Sum.inl (distinguishedSide (SegmentRootOriginal hT P optional i))
  else
    match hclass : segmentSourceClass hT P optional i with
    | Sum.inl q => Sum.inl (componentReservoirSide P q)
    | Sum.inr j => coordinateBranchSlot P S capacity0 capacity1 capacityb A
        edge0 edge1 edgeb orient j
        (segmentEndpointSide hT P optional i j
          ((AllocationHierarchy hT P optional).segments.root i))

/-- Slot of an individual hierarchy coordinate. -/
def coordinateHierarchyInteriorSlot
    (i : SegmentIndex hT P optional)
    (a : Fin ((AllocationHierarchy hT P optional).segments.size i)) :
    RootSlot Edge :=
  match hclass : segmentSourceClass hT P optional i with
  | Sum.inl q => Sum.inl (componentReservoirSide P q)
  | Sum.inr j => coordinateBranchSlot P S capacity0 capacity1 capacityb A
      edge0 edge1 edgeb orient j
      (segmentEndpointSide hT P optional i j a)

@[simp] theorem coordinateHierarchyRootSlot_distinguished
    (i : SegmentIndex hT P optional)
    (hi : SegmentRootOriginal hT P optional i ∈ distinguished) :
    coordinateHierarchyRootSlot hT P optional distinguished distinguishedSide S capacity0
        capacity1 capacityb A edge0 edge1 edgeb orient i =
      Sum.inl (distinguishedSide (SegmentRootOriginal hT P optional i)) := by
  simp [coordinateHierarchyRootSlot, hi]

@[simp] theorem coordinateHierarchyRootSlot_branch
    (i : SegmentIndex hT P optional) (j : BranchIndex P)
    (hi : SegmentRootOriginal hT P optional i ∉ distinguished)
    (hclass : segmentSourceClass hT P optional i = Sum.inr j) :
    coordinateHierarchyRootSlot hT P optional distinguished distinguishedSide S capacity0
        capacity1 capacityb A edge0 edge1 edgeb orient i =
      coordinateBranchSlot P S capacity0 capacity1 capacityb A edge0 edge1
        edgeb orient j
        (segmentEndpointSide hT P optional i j
          ((AllocationHierarchy hT P optional).segments.root i)) := by
  rw [coordinateHierarchyRootSlot, if_neg hi]
  generalize hc : segmentSourceClass hT P optional i = c
  cases c with
  | inl q =>
      have hbad : (Sum.inl q : Fin P.numParts ⊕ BranchIndex P) = Sum.inr j :=
        hc.symm.trans hclass
      cases hbad
  | inr k =>
      have hkj : k = j := Sum.inr.inj (hc.symm.trans hclass)
      subst k
      rfl

@[simp] theorem coordinateHierarchyRootSlot_component
    (i : SegmentIndex hT P optional) (q : Fin P.numParts)
    (hi : SegmentRootOriginal hT P optional i ∉ distinguished)
    (hclass : segmentSourceClass hT P optional i = Sum.inl q) :
    coordinateHierarchyRootSlot hT P optional distinguished distinguishedSide S
        capacity0 capacity1 capacityb A edge0 edge1 edgeb orient i =
      Sum.inl (componentReservoirSide P q) := by
  rw [coordinateHierarchyRootSlot, if_neg hi]
  generalize hc : segmentSourceClass hT P optional i = c
  cases c with
  | inl k =>
      have hkq : k = q := Sum.inl.inj (hc.symm.trans hclass)
      subst k
      rfl
  | inr j =>
      have hbad : (Sum.inr j : Fin P.numParts ⊕ BranchIndex P) = Sum.inl q :=
        hc.symm.trans hclass
      cases hbad

@[simp] theorem coordinateHierarchyInteriorSlot_branch
    (i : SegmentIndex hT P optional) (j : BranchIndex P)
    (hclass : segmentSourceClass hT P optional i = Sum.inr j)
    (a : Fin ((AllocationHierarchy hT P optional).segments.size i)) :
    coordinateHierarchyInteriorSlot hT P optional S capacity0
        capacity1 capacityb A edge0 edge1 edgeb orient i a =
      coordinateBranchSlot P S capacity0 capacity1 capacityb A edge0 edge1
        edgeb orient j (segmentEndpointSide hT P optional i j a) := by
  rw [coordinateHierarchyInteriorSlot]
  generalize hc : segmentSourceClass hT P optional i = c
  cases c with
  | inl q =>
      have hbad : (Sum.inl q : Fin P.numParts ⊕ BranchIndex P) = Sum.inr j :=
        hc.symm.trans hclass
      cases hbad
  | inr k =>
      have hkj : k = j := Sum.inr.inj (hc.symm.trans hclass)
      subst k
      rfl

@[simp] theorem coordinateHierarchyInteriorSlot_component
    (i : SegmentIndex hT P optional) (q : Fin P.numParts)
    (hclass : segmentSourceClass hT P optional i = Sum.inl q)
    (a : Fin ((AllocationHierarchy hT P optional).segments.size i)) :
    coordinateHierarchyInteriorSlot hT P optional S capacity0 capacity1
        capacityb A edge0 edge1 edgeb orient i a =
      Sum.inl (componentReservoirSide P q) := by
  rw [coordinateHierarchyInteriorSlot]
  generalize hc : segmentSourceClass hT P optional i = c
  cases c with
  | inl k =>
      have hkq : k = q := Sum.inl.inj (hc.symm.trans hclass)
      subst k
      rfl
  | inr j =>
      have hbad : (Sum.inr j : Fin P.numParts ⊕ BranchIndex P) = Sum.inl q :=
        hc.symm.trans hclass
      cases hbad

/-- Away from the distinguished A/B marks, a branch segment root uses the
same coordinate endpoint as its interior-slot view of that root. -/
theorem coordinateRootSlot_eq_interiorSlot_root
    (i : SegmentIndex hT P optional) (j : BranchIndex P)
    (hi : SegmentRootOriginal hT P optional i ∉ distinguished)
    (hclass : segmentSourceClass hT P optional i = Sum.inr j) :
    coordinateHierarchyRootSlot hT P optional distinguished distinguishedSide S capacity0
        capacity1 capacityb A edge0 edge1 edgeb orient i =
      coordinateHierarchyInteriorSlot hT P optional S capacity0
        capacity1 capacityb A edge0 edge1 edgeb orient i
          ((AllocationHierarchy hT P optional).segments.root i) := by
  rw [coordinateHierarchyRootSlot_branch hT P optional distinguished distinguishedSide S
      capacity0 capacity1 capacityb A edge0 edge1 edgeb orient i j hi hclass,
    coordinateHierarchyInteriorSlot_branch hT P optional S
      capacity0 capacity1 capacityb A edge0 edge1 edgeb orient i j hclass]

end Allocated

end Erdos547b.ZhaoClaim615HierarchicalCoordinateSourceLayout

#print axioms Erdos547b.ZhaoClaim615HierarchicalCoordinateSourceLayout.coordinateRootSlot_eq_interiorSlot_root
