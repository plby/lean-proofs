/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615SourceSelection
import ErdosProblems.Erdos547b.Claim616HierarchyAttachments

/-!
# A/B-root hierarchy layout for Zhao Lemma 6.15

Lemma 6.15 uses no intermediate `C` layer.  Component roots occupy the two
distinguished root reservoirs, while every root-deleted branch is assigned
to one matching edge.  The selected `F₀`, residual-major `F₁`, and minor
`F_b` classes use three disjoint allocation budgets, but their edge maps are
transported to one physical matching type before collision accounting.

The allocation theorem below is purely finite bin packing.  The layout then
gives the exact root slot, interior slot, and physical pool maps consumed by
the target-unified hierarchy backend.  It contains no host copy or
containment field.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615HierarchicalSourceLayout

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ForestMatching
open Erdos547b.ZhaoClaim68ParityHalf
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim616HierarchicalSourceLayout
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoLemma59SpecialSegmentation
open Erdos547b.ZhaoLemma59HierarchicalUnified

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

abbrev BranchIndex (P : ZhaoForestPartition T globalRoot small) :=
  Fin (Fintype.card (ChildKey P.orderedForest))

/-- Major branches left after the Lemma-6.15 exceptional root-subforest. -/
def majorResidualBranches
    (P : ZhaoForestPartition T globalRoot small)
    {available : Finset (BranchIndex P)} {target slack : ℕ}
    (S : SelectedF0 P available target slack) : Finset (BranchIndex P) :=
  halfBranches P \ S.selected

@[simp] theorem mem_majorResidualBranches
    (P : ZhaoForestPartition T globalRoot small)
    {available : Finset (BranchIndex P)} {target slack : ℕ}
    (S : SelectedF0 P available target slack) (j : BranchIndex P) :
    j ∈ majorResidualBranches P S ↔
      j ∈ halfBranches P ∧ j ∉ S.selected := by
  simp [majorResidualBranches]

/-- Exact source mass partition after selecting `F₀`. -/
theorem selected_add_residual_add_minor_mass
    (P : ZhaoForestPartition T globalRoot small)
    {available : Finset (BranchIndex P)} {target slack : ℕ}
    (S : SelectedF0 P available target slack)
    (havailable : available ⊆ halfBranches P) :
    branchMass P S.selected + branchMass P (majorResidualBranches P S) +
        branchMass P (minorBranches P) =
      OrderedBranchForest.edgeDemand (branchForest P) := by
  have hselected : S.selected ⊆ halfBranches P :=
    S.selected_available.trans havailable
  rw [branchMass, branchMass, branchMass,
    OrderedBranchForest.edgeDemand, majorResidualBranches]
  rw [← Finset.sum_union Finset.disjoint_sdiff,
    Finset.union_sdiff_of_subset hselected]
  rw [← Finset.sum_union (halfBranches_disjoint_minorBranches P),
    halfBranches_union_minorBranches]
  simp

/-- Branch-coherent matching allocation for the three source classes. -/
structure SourceAllocation
    (P : ZhaoForestPartition T globalRoot small)
    {available : Finset (BranchIndex P)} {target slack : ℕ}
    (S : SelectedF0 P available target slack)
    (K0 K1 Kb : Type*)
    [Fintype K0] [DecidableEq K0]
    [Fintype K1] [DecidableEq K1]
    [Fintype Kb] [DecidableEq Kb]
    (capacity0 : K0 → ℕ) (capacity1 : K1 → ℕ)
    (capacityb : Kb → ℕ) where
  F0edge : BranchIndex P → K0
  F1edge : BranchIndex P → K1
  Fbedge : BranchIndex P → Kb
  F0_load : ∀ e : K0,
    ∑ j ∈ S.selected.filter (F0edge · = e),
      (branchForest P).branches.size j ≤ capacity0 e
  F1_load : ∀ e : K1,
    ∑ j ∈ (majorResidualBranches P S).filter (F1edge · = e),
      (branchForest P).branches.size j ≤ capacity1 e
  Fb_load : ∀ e : Kb,
    ∑ j ∈ (minorBranches P).filter (Fbedge · = e),
      (branchForest P).branches.size j ≤ capacityb e

/-- The actual three finite packings.  The three displayed aggregate
capacity inequalities are the only source-allocation inputs. -/
theorem exists_sourceAllocation
    (P : ZhaoForestPartition T globalRoot small)
    {available : Finset (BranchIndex P)} {target slack : ℕ}
    (S : SelectedF0 P available target slack)
    (K0 K1 Kb : Type*)
    [Fintype K0] [DecidableEq K0] [Nonempty K0]
    [Fintype K1] [DecidableEq K1] [Nonempty K1]
    [Fintype Kb] [DecidableEq Kb] [Nonempty Kb]
    (capacity0 : K0 → ℕ) (capacity1 : K1 → ℕ)
    (capacityb : Kb → ℕ)
    (hbudget0 : branchMass P S.selected + Fintype.card K0 * small ≤
      ∑ e : K0, capacity0 e)
    (hbudget1 : branchMass P (majorResidualBranches P S) +
        Fintype.card K1 * small ≤ ∑ e : K1, capacity1 e)
    (hbudgetb : branchMass P (minorBranches P) +
        Fintype.card Kb * small ≤ ∑ e : Kb, capacityb e) :
    Nonempty (SourceAllocation P S K0 K1 Kb capacity0 capacity1 capacityb) := by
  classical
  have hsmall (j : BranchIndex P) :
      (branchForest P).branches.size j ≤ small :=
    canonical_branch_size_le_small P j
  obtain ⟨f0, hf0⟩ := capacity_packing S.selected
    (branchForest P).branches.size capacity0 small
    (fun j _ => hsmall j) (by simpa [branchMass] using hbudget0)
  obtain ⟨f1, hf1⟩ := capacity_packing (majorResidualBranches P S)
    (branchForest P).branches.size capacity1 small
    (fun j _ => hsmall j) (by simpa [branchMass] using hbudget1)
  obtain ⟨fb, hfb⟩ := capacity_packing (minorBranches P)
    (branchForest P).branches.size capacityb small
    (fun j _ => hsmall j) (by simpa [branchMass] using hbudgetb)
  exact ⟨{
    F0edge := f0
    F1edge := f1
    Fbedge := fb
    F0_load := hf0
    F1_load := hf1
    Fb_load := hfb
  }⟩

/-! ## Physical hierarchy layout -/

/-- Root candidate slots: a distinguished A/B reservoir or an oriented
endpoint of a physical matching edge. -/
abbrev RootSlot (Edge : Type*) := Sum (Fin 2) (Edge × Fin 2)

/-- Collision pools forget only the orientation of a matching edge. -/
abbrev PhysicalPool (Edge : Type*) := Sum (Fin 2) Edge

def rootSlotPool {Edge : Type*} : RootSlot Edge → PhysicalPool Edge
  | Sum.inl side => Sum.inl side
  | Sum.inr ⟨e, _⟩ => Sum.inr e

/-- The distinguished reservoir prescribed by the literal parity of a
source vertex.  Adjacent source vertices receive opposite reservoirs. -/
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
  split <;> split <;> simp_all

/-! ## All-vertex segmentation

For Lemma 5.8 the matching capacity is an endpoint capacity, rather than a
capacity of the underlying unoriented edge.  We therefore expose every
non-global source vertex as its own hierarchy segment.  The resulting
`poolLoad` counts literal source vertices in the assigned oriented slot
exactly; in particular it does not charge a whole branch to both endpoints.
-/

/-- Every coordinate of the one-root branch forest is marked when the
optional source set is `univ`. -/
theorem allVertex_coordinate_mem_marks
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (j : Fin (Fintype.card (ChildKey (wholeOrderedTree T hT globalRoot))))
    (a : Fin ((wholeBranchForest T hT globalRoot).branches.size j)) :
    (⟨j, a⟩ : BranchVertex (wholeBranchForest T hT globalRoot)) ∈
      marks (wholeBranchForest T hT globalRoot)
        (AllocationSpecial hT P Finset.univ) := by
  apply wholeBranchCoordinate_mem_marks_of_literal_marked hT P Finset.univ
  simp [zhaoMarkedVertices]

/-- Exposing every literal non-global vertex makes every hierarchy segment
a singleton. -/
theorem allVertex_segment_size_eq_one
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (i : SegmentIndex hT P Finset.univ) :
    (AllocationHierarchy hT P Finset.univ).segments.size i = 1 := by
  let F := wholeBranchForest T hT globalRoot
  let special := AllocationSpecial hT P Finset.univ
  let f : Fin ((AllocationHierarchy hT P Finset.univ).segments.size i) →
      Unit := fun _ ↦ ()
  have hf : Function.Injective f := by
    intro a b _
    let q : BranchVertex F := (markEnum F special i).1
    have haMark :
        (⟨q.1, (fiberEquiv F special i a).1⟩ : BranchVertex F) ∈
          marks F special := by
      exact allVertex_coordinate_mem_marks hT P q.1
        (fiberEquiv F special i a).1
    have hbMark :
        (⟨q.1, (fiberEquiv F special i b).1⟩ : BranchVertex F) ∈
          marks F special := by
      exact allVertex_coordinate_mem_marks hT P q.1
        (fiberEquiv F special i b).1
    have haVal : (fiberEquiv F special i a).1 = q.2 := by
      have hself := nearestMark_eq_self_of_mem F special q.1 haMark
      exact hself.symm.trans (fiberEquiv F special i a).2
    have hbVal : (fiberEquiv F special i b).1 = q.2 := by
      have hself := nearestMark_eq_self_of_mem F special q.1 hbMark
      exact hself.symm.trans (fiberEquiv F special i b).2
    apply (fiberEquiv F special i).injective
    exact Subtype.ext (haVal.trans hbVal.symm)
  have hle := Fintype.card_le_of_injective f hf
  have hpos := segmented_size_pos (wholeBranchForest T hT globalRoot)
    (AllocationSpecial hT P Finset.univ) i
  simpa only [Fintype.card_fin, Fintype.card_unit] at hle
  omega

/-- On the all-vertex hierarchy, unified occupancy is exactly the number of
segment roots assigned to the displayed (possibly oriented) pool. -/
theorem allVertex_poolLoad_eq_card_filter
    {Pool : Type*} [DecidableEq Pool]
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (rootPool interiorPool :
      SegmentIndex hT P Finset.univ → Pool) (p : Pool) :
    (AllocationHierarchy hT P Finset.univ).poolLoad rootPool interiorPool p =
      #(Finset.univ.filter fun i ↦ rootPool i = p) := by
  rw [Erdos547b.ZhaoLemma59HierarchicalUnified.HierarchicalSegmentForest.poolLoad,
    Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  rw [Erdos547b.ZhaoLemma59HierarchicalUnified.HierarchicalSegmentForest.poolWeight,
    allVertex_segment_size_eq_one hT P i]
  simp

section Allocated

variable
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
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

/-- Physical matching edge inherited by every segment of a branch. -/
def branchEdge (j : BranchIndex P) : Edge :=
  if _hj0 : j ∈ S.selected then edge0 (A.F0edge j)
  else if _hj1 : j ∈ majorResidualBranches P S then edge1 (A.F1edge j)
  else edgeb (A.Fbedge j)

/-- Source-facing endpoint inherited by every segment of a branch. -/
def branchRootSide (j : BranchIndex P) : Fin 2 :=
  if _hj0 : j ∈ S.selected then rootSide0 (A.F0edge j)
  else if _hj1 : j ∈ majorResidualBranches P S then rootSide1 (A.F1edge j)
  else rootSideb (A.Fbedge j)

/-- Component-root segments and optional Lemma-6.3 cut parents use A/B.
Every other genuine branch segment starts in the source-facing endpoint of
its assigned matching edge. -/
def hierarchyRootSlotWithDistinguished
    (distinguished : Finset V)
    (i : SegmentIndex hT P optional) : RootSlot Edge :=
  if SegmentRootOriginal hT P optional i ∈ distinguished then
    Sum.inl (sourceVertexReservoirSide P
      (SegmentRootOriginal hT P optional i))
  else
    match segmentSourceClass hT P optional i with
    | Sum.inl q => Sum.inl (componentReservoirSide P q)
    | Sum.inr j => Sum.inr ⟨
        branchEdge P S capacity0 capacity1 capacityb A edge0 edge1 edgeb j,
        orientedSide
          (branchRootSide P S capacity0 capacity1 capacityb A rootSide0
            rootSide1 rootSideb j)
          (segmentEndpointSide hT P optional i j
            ((AllocationHierarchy hT P optional).segments.root i))⟩

/-- Backwards-compatible layout in which every optional segmentation mark is
also required to occupy a distinguished reservoir. -/
def hierarchyRootSlot (i : SegmentIndex hT P optional) : RootSlot Edge :=
  hierarchyRootSlotWithDistinguished hT P optional S capacity0 capacity1
    capacityb A edge0 edge1 edgeb rootSide0 rootSide1 rootSideb optional i

def hierarchyRootPool (i : SegmentIndex hT P optional) : PhysicalPool Edge :=
  rootSlotPool (hierarchyRootSlot hT P optional S capacity0 capacity1
    capacityb A edge0 edge1 edgeb rootSide0 rootSide1 rootSideb i)

/-- All coordinates of one branch segment charge the same physical edge. -/
def hierarchyInteriorPool (i : SegmentIndex hT P optional) :
    PhysicalPool Edge :=
  match segmentSourceClass hT P optional i with
  | Sum.inl q => Sum.inl (componentReservoirSide P q)
  | Sum.inr j => Sum.inr
      (branchEdge P S capacity0 capacity1 capacityb A edge0 edge1 edgeb j)

/-- Matching endpoint occupied by a segment coordinate, oriented from the
source-facing endpoint chosen for its canonical branch. -/
def hierarchyInteriorSlot
    (i : SegmentIndex hT P optional)
    (a : Fin ((AllocationHierarchy hT P optional).segments.size i)) :
    RootSlot Edge :=
  match hclass : segmentSourceClass hT P optional i with
  | Sum.inl q => Sum.inl (componentReservoirSide P q)
  | Sum.inr j =>
      Sum.inr ⟨
        branchEdge P S capacity0 capacity1 capacityb A edge0 edge1 edgeb j,
        orientedSide
          (branchRootSide P S capacity0 capacity1 capacityb A rootSide0
            rootSide1 rootSideb j)
          (segmentEndpointSide hT P optional i j a)⟩

/-- Exact oriented root slot for the all-vertex Lemma-6.15 segmentation.
Only the displayed source vertices are redirected to an A/B reservoir;
every other literal vertex keeps the endpoint side dictated by its distance
inside its assigned canonical branch. -/
abbrev allVertexRootSlot
    (distinguished : Finset V)
    (i : SegmentIndex hT P Finset.univ) : RootSlot Edge :=
  hierarchyRootSlotWithDistinguished hT P Finset.univ S capacity0 capacity1
    capacityb A edge0 edge1 edgeb rootSide0 rootSide1 rootSideb
    distinguished i

/-- Every all-vertex segment is a singleton, so its sole interior-coordinate
slot is definitionally chosen to be its root slot.  This is the exact
`interior_pool` equality required by the unified realizer and introduces no
extra host candidate. -/
def allVertexInteriorSlot
    (distinguished : Finset V)
    (i : SegmentIndex hT P Finset.univ)
    (_a : Fin ((AllocationHierarchy hT P Finset.univ).segments.size i)) :
    RootSlot Edge :=
  allVertexRootSlot hT P S capacity0 capacity1 capacityb A edge0 edge1 edgeb
    rootSide0 rootSide1 rootSideb distinguished i

@[simp] theorem allVertexInteriorSlot_eq_rootSlot
    (distinguished : Finset V)
    (i : SegmentIndex hT P Finset.univ)
    (a : Fin ((AllocationHierarchy hT P Finset.univ).segments.size i)) :
    allVertexInteriorSlot hT P S capacity0 capacity1 capacityb A edge0 edge1
        edgeb rootSide0 rootSide1 rootSideb distinguished i a =
      allVertexRootSlot hT P S capacity0 capacity1 capacityb A edge0 edge1
        edgeb rootSide0 rootSide1 rootSideb distinguished i :=
  rfl

/-- Exact all-vertex occupancy of an oriented root slot. -/
theorem allVertex_oriented_poolLoad_eq_card_filter
    (distinguished : Finset V) (slot : RootSlot Edge) :
    (AllocationHierarchy hT P Finset.univ).poolLoad
        (allVertexRootSlot hT P S capacity0 capacity1 capacityb A edge0 edge1
          edgeb rootSide0 rootSide1 rootSideb distinguished)
        (fun i ↦ allVertexInteriorSlot hT P S capacity0 capacity1 capacityb A
          edge0 edge1 edgeb rootSide0 rootSide1 rootSideb distinguished i
            ((AllocationHierarchy hT P Finset.univ).segments.root i)) slot =
      #(Finset.univ.filter fun i ↦
        allVertexRootSlot hT P S capacity0 capacity1 capacityb A edge0 edge1
          edgeb rootSide0 rootSide1 rootSideb distinguished i = slot) := by
  apply allVertex_poolLoad_eq_card_filter hT P

@[simp] theorem rootSlotPool_hierarchyInteriorSlot
    (i : SegmentIndex hT P optional)
    (a : Fin ((AllocationHierarchy hT P optional).segments.size i)) :
    rootSlotPool (hierarchyInteriorSlot hT P optional S capacity0 capacity1
      capacityb A edge0 edge1 edgeb rootSide0 rootSide1 rootSideb i a) =
      hierarchyInteriorPool hT P optional S capacity0 capacity1 capacityb A
        edge0 edge1 edgeb i := by
  cases hclass : segmentSourceClass hT P optional i with
  | inl q =>
      simp [hierarchyInteriorSlot, hierarchyInteriorPool, hclass]
  | inr j =>
      simp [hierarchyInteriorSlot, hierarchyInteriorPool, hclass,
        branchEdge]

end Allocated

end Erdos547b.ZhaoClaim615HierarchicalSourceLayout

#print axioms Erdos547b.ZhaoClaim615HierarchicalSourceLayout.exists_sourceAllocation
#print axioms Erdos547b.ZhaoClaim615HierarchicalSourceLayout.rootSlotPool_hierarchyInteriorSlot
