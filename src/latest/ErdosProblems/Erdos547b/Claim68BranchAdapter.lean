/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616SourceBridge
import ErdosProblems.Erdos547b.Claim712NaturalSubtree
import ErdosProblems.Erdos547b.ForestCapacity

/-!
# Root-deleted branches of an ordered rooted forest

This is the source adapter used by Claims 6.16 and 6.17.  A branch is the
descendant set below one child of one component root.  Distinct branches are
disjoint, and each branch is reindexed as an actual rooted tree.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoClaim68BranchAdapter

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma59Part2Full
open SimpleGraphRose547

universe u

abbrev ForestVertex {r : ℕ} (F : OrderedRootedForest r) :=
  Σ i, Fin (F.size i)

/-- A component together with one child of its root. -/
abbrev ChildKey {r : ℕ} (F : OrderedRootedForest r) :=
  {z : ForestVertex F //
    (F.tree z.1).Adj (F.root z.1) z.2}

/-- The child keys are finite.  Their adjacency predicate is classically
decidable, so expose the noncomputable `Fintype` instance used by the
canonical `Fin` numbering below. -/
noncomputable instance childKeyFintype {r : ℕ}
    (F : OrderedRootedForest r) : Fintype (ChildKey F) :=
  Fintype.ofFinite (ChildKey F)

noncomputable def childKeyEquiv {r : ℕ} (F : OrderedRootedForest r) :
    Fin (Fintype.card (ChildKey F)) ≃ ChildKey F :=
  (Fintype.equivFin (ChildKey F)).symm

/-- The sigma-typed vertices below one root child. -/
def branchSet {r : ℕ} (F : OrderedRootedForest r)
    (j : Fin (Fintype.card (ChildKey F))) : Set (ForestVertex F) :=
  {z | z.1 = (childKeyEquiv F j).1.1 ∧
    ∃ h : z.1 = (childKeyEquiv F j).1.1,
      h ▸ z.2 ∈ rootedDescendants
        (F.tree (childKeyEquiv F j).1.1)
        (F.root (childKeyEquiv F j).1.1)
        (childKeyEquiv F j).1.2}

/-- Local descendant coordinates are exactly the vertices of the sigma
branch set. -/
noncomputable def branchSetEquiv {r : ℕ} (F : OrderedRootedForest r)
    (j : Fin (Fintype.card (ChildKey F))) :
    {a // a ∈ rootedDescendants
      (F.tree (childKeyEquiv F j).1.1)
      (F.root (childKeyEquiv F j).1.1)
      (childKeyEquiv F j).1.2} ≃
      {z // z ∈ branchSet F j} :=
  Equiv.ofBijective
    (fun a ↦ ⟨⟨(childKeyEquiv F j).1.1, a.1⟩,
      ⟨rfl, ⟨rfl, a.2⟩⟩⟩)
    ⟨by
      intro a b hab
      apply Subtype.ext
      exact eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Subtype.val hab)).2,
    by
      rintro ⟨⟨i, a⟩, hi, h, ha⟩
      cases hi
      have hh : h = rfl := Subsingleton.elim _ _
      cases hh
      exact ⟨⟨a, ha⟩, rfl⟩⟩

theorem anyRoot_not_mem_branchSet {r : ℕ} (F : OrderedRootedForest r)
    (i : Fin r) (j : Fin (Fintype.card (ChildKey F))) :
    (⟨i, F.root i⟩ : ForestVertex F) ∉ branchSet F j := by
  rintro ⟨hi, h, hr⟩
  cases hi
  have hh : h = rfl := Subsingleton.elim _ _
  cases hh
  have hc := (childKeyEquiv F j).2
  exact root_not_mem_rootedDescendants_child
    ⟨hc, by simpa using (F.tree _).dist_eq_one_iff_adj.mpr hc⟩ hr

/-- Transport an actual rooted-branch vertex across equality of component
indices.  Packaging every dependent coordinate as an explicit argument keeps
the equality eliminator out of the later sigma bookkeeping. -/
theorem transport_rootedBranch {r : ℕ} (F : OrderedRootedForest r)
    {i l : Fin r} (h : i = l)
    (child vertex : Fin (F.size l))
    (hchild : (F.tree l).Adj (F.root l) child)
    (hvertex : vertex ∈ rootedDescendants (F.tree l) (F.root l) child) :
    ∃ (child' vertex' : Fin (F.size i)),
      (F.tree i).Adj (F.root i) child' ∧
      vertex' ∈ rootedDescendants (F.tree i) (F.root i) child' ∧
      child'.val = child.val ∧ vertex'.val = vertex.val := by
  subst l
  exact ⟨child, vertex, hchild, hvertex, rfl, rfl⟩

theorem cast_fin_val {r : ℕ} (F : OrderedRootedForest r)
    {i l : Fin r} (h : i = l) (a : Fin (F.size i)) :
    (h ▸ a).val = a.val := by
  subst l
  rfl

theorem branchSet_disjoint {r : ℕ} (F : OrderedRootedForest r)
    {j l : Fin (Fintype.card (ChildKey F))} (hjl : j ≠ l) :
    Disjoint (branchSet F j) (branchSet F l) := by
  classical
  rw [Set.disjoint_left]
  intro z hzj hzl
  rcases hzj with ⟨hjcomp, hjtransport, hzj⟩
  rcases hzl with ⟨hlcomp, hltransport, hzl⟩
  have hcomp : (childKeyEquiv F j).1.1 =
      (childKeyEquiv F l).1.1 := hjcomp.symm.trans hlcomp
  let zj : Fin (F.size (childKeyEquiv F j).1.1) := hjtransport ▸ z.2
  obtain ⟨childL, zl, hlAdj, hzl', hchildLVal, hzlVal⟩ :=
    transport_rootedBranch F hcomp (childKeyEquiv F l).1.2
      (hltransport ▸ z.2) (childKeyEquiv F l).2 hzl
  have hzlzj : zl = zj := by
    apply Fin.ext
    exact hzlVal.trans ((cast_fin_val F hltransport z.2).trans
      (cast_fin_val F hjtransport z.2).symm)
  subst zl
  have hchild : (childKeyEquiv F j).1.2 =
      childL := by
    by_contra hne
    have hjChild : IsChild (F.tree (childKeyEquiv F j).1.1)
        (F.root (childKeyEquiv F j).1.1)
        (F.root (childKeyEquiv F j).1.1)
        (childKeyEquiv F j).1.2 :=
      ⟨(childKeyEquiv F j).2,
        by simpa using
          (F.tree _).dist_eq_one_iff_adj.mpr (childKeyEquiv F j).2⟩
    have hlChild : IsChild (F.tree (childKeyEquiv F j).1.1)
        (F.root (childKeyEquiv F j).1.1)
        (F.root (childKeyEquiv F j).1.1)
        childL :=
      ⟨hlAdj, by simpa using (F.tree _).dist_eq_one_iff_adj.mpr hlAdj⟩
    have hd := disjoint_rootedDescendants_of_distinct_children
      (F.isTree _) hjChild hlChild hne
    apply (Finset.disjoint_left.mp hd)
      (by simpa only [zj] using hzj)
      hzl'
  have hkey : childKeyEquiv F j = childKeyEquiv F l := by
    apply Subtype.ext
    apply Sigma.ext hcomp
    apply (Fin.heq_ext_iff (by rw [hcomp])).mpr
    exact (congrArg Fin.val hchild).trans hchildLVal
  exact hjl ((childKeyEquiv F).injective hkey)

/-! ## The branches partition the non-root coordinates -/

abbrev NonRootCoordinate {r : ℕ} (F : OrderedRootedForest r) :=
  {z : ForestVertex F // z.2 ≠ F.root z.1}

abbrev BranchSetVertex {r : ℕ} (F : OrderedRootedForest r) :=
  Σ j : Fin (Fintype.card (ChildKey F)), {z // z ∈ branchSet F j}

/-- Forget the branch label.  Membership in a rooted-descendant branch
certifies that the resulting coordinate is not a component root. -/
noncomputable def branchSetFlatten {r : ℕ} (F : OrderedRootedForest r) :
    BranchSetVertex F → NonRootCoordinate F := fun x ↦
  ⟨x.2.1, by
    intro hroot
    have hx : x.2.1 =
        (⟨x.2.1.1, F.root x.2.1.1⟩ : ForestVertex F) :=
      Sigma.ext rfl (heq_of_eq hroot)
    exact anyRoot_not_mem_branchSet F x.2.1.1 x.1 (hx ▸ x.2.2)⟩

theorem branchSetFlatten_injective {r : ℕ} (F : OrderedRootedForest r) :
    Function.Injective (branchSetFlatten F) := by
  rintro ⟨j, z⟩ ⟨l, w⟩ h
  have hzw : z.1 = w.1 := congrArg Subtype.val h
  have hjl : j = l := by
    by_contra hjl
    have hmeml : z.1 ∈ branchSet F l := hzw.symm ▸ w.2
    exact (Set.disjoint_left.mp (branchSet_disjoint F hjl)) z.2 hmeml
  subst l
  have hsub : z = w := Subtype.ext hzw
  subst w
  rfl

theorem branchSetFlatten_surjective {r : ℕ} (F : OrderedRootedForest r) :
    Function.Surjective (branchSetFlatten F) := by
  intro z
  obtain ⟨a, ha, -⟩ :=
    existsUnique_child_rootedBranch (F.isTree z.1.1) (F.root z.1.1) z.2
  let key : ChildKey F := ⟨⟨z.1.1, a⟩, ha.1.1⟩
  let j : Fin (Fintype.card (ChildKey F)) := (childKeyEquiv F).symm key
  have hj : childKeyEquiv F j = key := Equiv.apply_symm_apply _ _
  have hzBranch : z.1 ∈ branchSet F j := by
    change z.1.1 = (childKeyEquiv F j).1.1 ∧
      ∃ h : z.1.1 = (childKeyEquiv F j).1.1,
        h ▸ z.1.2 ∈ rootedDescendants
          (F.tree (childKeyEquiv F j).1.1)
          (F.root (childKeyEquiv F j).1.1)
          (childKeyEquiv F j).1.2
    rw [hj]
    exact ⟨rfl, ⟨rfl, ha.2⟩⟩
  refine ⟨⟨j, ⟨z.1, hzBranch⟩⟩, ?_⟩
  apply Subtype.ext
  rfl

/-- Canonical branch coordinates are equivalent to all non-root coordinates
of the original ordered forest. -/
noncomputable def branchSetEquivNonroots {r : ℕ}
    (F : OrderedRootedForest r) :
    BranchSetVertex F ≃ NonRootCoordinate F :=
  Equiv.ofBijective (branchSetFlatten F)
    ⟨branchSetFlatten_injective F, branchSetFlatten_surjective F⟩

def branchLocalGraph {r : ℕ} (F : OrderedRootedForest r)
    (j : Fin (Fintype.card (ChildKey F))) :
    SimpleGraph {a // a ∈ rootedDescendants
      (F.tree (childKeyEquiv F j).1.1)
      (F.root (childKeyEquiv F j).1.1)
      (childKeyEquiv F j).1.2} :=
  (F.tree (childKeyEquiv F j).1.1).induce _

theorem branchInduce_isTree {r : ℕ} (F : OrderedRootedForest r)
    (j : Fin (Fintype.card (ChildKey F))) :
    (branchLocalGraph F j).IsTree := by
  let i := (childKeyEquiv F j).1.1
  let c := (childKeyEquiv F j).1.2
  have hconn : ((F.tree i).induce
      (rootedDescendants (F.tree i) (F.root i) c : Set _)).Connected :=
    connected_induce_rootedDescendants (F.isTree i) (F.root i) c
  have hacyc : ((F.tree i).induce
      (rootedDescendants (F.tree i) (F.root i) c : Set _)).IsAcyclic := by
    let e : ((F.tree i).induce
        (rootedDescendants (F.tree i) (F.root i) c : Set _)) ↪g
        F.tree i := SimpleGraph.Embedding.induce _
    exact SimpleGraph.IsAcyclic.comap e e.injective (F.isTree i).isAcyclic
  exact ⟨hconn, hacyc⟩

noncomputable def branchCoordinateEquiv {r : ℕ}
    (F : OrderedRootedForest r)
    (j : Fin (Fintype.card (ChildKey F))) :
    Fin (Nat.card {z // z ∈ branchSet F j}) ≃
      {z // z ∈ branchSet F j} :=
  (Finite.equivFin {z // z ∈ branchSet F j}).symm

noncomputable def branchVertexEquiv {r : ℕ}
    (F : OrderedRootedForest r)
    (j : Fin (Fintype.card (ChildKey F))) :=
  branchCoordinateEquiv F j

/-- The ordered family of all root-deleted branches. -/
noncomputable def toOrderedBranchForest {r : ℕ}
    (F : OrderedRootedForest r) :
    OrderedBranchForest r (Fintype.card (ChildKey F)) where
  branches :=
    { size := fun j => Nat.card {z // z ∈ branchSet F j}
      tree := fun j => (branchLocalGraph F j).comap
        ((branchCoordinateEquiv F j).trans (branchSetEquiv F j).symm)
      isTree := fun j => by
        exact (SimpleGraph.Iso.comap
          ((branchCoordinateEquiv F j).trans (branchSetEquiv F j).symm)
          (branchLocalGraph F j)).isTree_iff.mpr (branchInduce_isTree F j)
      root := fun j => (branchCoordinateEquiv F j).symm
        ((branchSetEquiv F j)
          ⟨(childKeyEquiv F j).1.2,
            self_mem_rootedDescendants _ _ _⟩) }
  owner := fun j => (childKeyEquiv F j).1.1

/-- The `Fin`-numbered branch coordinates used by `OrderedBranchForest` are
exactly all non-root coordinates of the input ordered forest. -/
noncomputable def branchCoordinatesEquivNonroots {r : ℕ}
    (F : OrderedRootedForest r) :
    (Σ j, Fin ((toOrderedBranchForest F).branches.size j)) ≃
      NonRootCoordinate F :=
  (Equiv.sigmaCongrRight fun j ↦ branchCoordinateEquiv F j).trans
    (branchSetEquivNonroots F)

@[simp] theorem branchCoordinatesEquivNonroots_component {r : ℕ}
    (F : OrderedRootedForest r)
    (j : Fin (Fintype.card (ChildKey F)))
    (a : Fin ((toOrderedBranchForest F).branches.size j)) :
    (branchCoordinatesEquivNonroots F ⟨j, a⟩).1.1 =
      (toOrderedBranchForest F).owner j := by
  change (branchCoordinateEquiv F j a).1.1 =
    (childKeyEquiv F j).1.1
  exact (branchCoordinateEquiv F j a).2.1

@[simp] theorem toOrderedBranchForest_size {r : ℕ}
    (F : OrderedRootedForest r)
    (j : Fin (Fintype.card (ChildKey F))) :
    (toOrderedBranchForest F).branches.size j =
      Nat.card {z // z ∈ branchSet F j} := rfl

@[simp] theorem branchVertexEquiv_root {r : ℕ}
    (F : OrderedRootedForest r)
    (j : Fin (Fintype.card (ChildKey F))) :
    branchVertexEquiv F j ((toOrderedBranchForest F).branches.root j) =
      (branchSetEquiv F j)
        ⟨(childKeyEquiv F j).1.2,
          self_mem_rootedDescendants _ _ _⟩ := by
  exact Equiv.apply_symm_apply _ _

end Erdos547b.ZhaoClaim68BranchAdapter

#print axioms Erdos547b.ZhaoClaim68BranchAdapter.branchSet_disjoint
#print axioms Erdos547b.ZhaoClaim68BranchAdapter.branchInduce_isTree
