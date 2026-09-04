/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma59Part2Full
import ErdosProblems.Erdos547b.HierarchicalSegmentForest
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoLemma59SpecialSegmentation

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoLemma59Hierarchical

universe u

variable {r b : ℕ}

abbrev BranchVertex (F : OrderedBranchForest r b) :=
  Σ j, Fin (F.branches.size j)

/-- Forget impossible original-root entries and retain the branch coordinates
of a source optional set. -/
def branchSpecial (F : OrderedBranchForest r b) (special : Finset F.Vertex) :
    Finset (BranchVertex F) :=
  Finset.univ.filter fun z ↦ (Sum.inr z : F.Vertex) ∈ special

@[simp] theorem mem_branchSpecial (F : OrderedBranchForest r b)
    (special : Finset F.Vertex) (z : BranchVertex F) :
    z ∈ branchSpecial F special ↔ (Sum.inr z : F.Vertex) ∈ special := by
  simp [branchSpecial]

theorem card_branchSpecial_le (F : OrderedBranchForest r b)
    (special : Finset F.Vertex) : #(branchSpecial F special) ≤ #special := by
  let image : Finset F.Vertex := (branchSpecial F special).image Sum.inr
  have hsub : image ⊆ special := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨z, hz, rfl⟩
    exact (mem_branchSpecial F special z).mp hz
  have hcard : #image = #(branchSpecial F special) := by
    rw [Finset.card_image_iff.mpr]
    intro x _ y _ h
    exact Sum.inr.inj h
  exact hcard.symm.trans_le (Finset.card_le_card hsub)

/-- The cluster-layer vertices after exposing `special`: every old Level1
branch root, together with the requested additional odd vertices. -/
def marks (F : OrderedBranchForest r b) (special : Finset (BranchVertex F)) :
    Finset (BranchVertex F) :=
  Finset.univ.image (fun j ↦ ⟨j, F.branches.root j⟩) ∪ special

theorem branchRoot_mem_marks (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) (j : Fin b) :
    (⟨j, F.branches.root j⟩ : BranchVertex F) ∈ marks F special := by
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

theorem special_subset_marks (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) : special ⊆ marks F special := by
  intro z hz
  exact Finset.mem_union_right _ hz

theorem card_marks_le (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) :
    #(marks F special) ≤ b + #special := by
  calc
    #(marks F special) ≤
        #(Finset.univ.image (fun j : Fin b ↦
          (⟨j, F.branches.root j⟩ : BranchVertex F))) + #special := by
      exact Finset.card_union_le _ _
    _ = b + #special := by
      congr 1
      rw [Finset.card_image_iff.mpr]
      · simp
      · intro i _ j _ h
        exact (Sigma.mk.inj_iff.mp h).1

theorem card_marks_branchSpecial_le (F : OrderedBranchForest r b)
    (special : Finset F.Vertex) :
    #(marks F (branchSpecial F special)) ≤ b + #special :=
  (card_marks_le F (branchSpecial F special)).trans
    (Nat.add_le_add_left (card_branchSpecial_le F special) b)

theorem card_branchRoots_le_marks (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) : b ≤ #(marks F special) := by
  let R : Finset (BranchVertex F) :=
    Finset.univ.image (fun j ↦ ⟨j, F.branches.root j⟩)
  have hsub : R ⊆ marks F special := by
    intro z hz
    exact Finset.mem_union_left _ hz
  have hcard : #R = b := by
    rw [Finset.card_image_iff.mpr]
    · simp [R]
    · intro i _ j _ h
      exact (Sigma.mk.inj_iff.mp h).1
  exact hcard.symm.trans_le (Finset.card_le_card hsub)

/-- Nearest marked ancestor in a rooted branch. -/
noncomputable def nearestMark (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) (j : Fin b)
    (a : Fin (F.branches.size j)) : Fin (F.branches.size j) := by
  classical
  exact if ha : (⟨j, a⟩ : BranchVertex F) ∈ marks F special then a
    else
      have haroot : a ≠ F.branches.root j := by
        intro h
        apply ha
        subst a
        exact branchRoot_mem_marks F special j
      nearestMark F special j
        (TreePartition.parent (F.branches.isTree j) (F.branches.root j) haroot)
termination_by (F.branches.tree j).dist (F.branches.root j) a
decreasing_by
  have hp := TreePartition.parent_dist_add_one
    (F.branches.isTree j) (F.branches.root j) haroot
  omega

theorem nearestMark_eq_self_of_mem (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) (j : Fin b)
    {a : Fin (F.branches.size j)}
    (ha : (⟨j, a⟩ : BranchVertex F) ∈ marks F special) :
    nearestMark F special j a = a := by
  rw [nearestMark.eq_def]
  simp [ha]

theorem nearestMark_eq_parent_of_not_mem (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) (j : Fin b)
    {a : Fin (F.branches.size j)}
    (ha : (⟨j, a⟩ : BranchVertex F) ∉ marks F special)
    (haroot : a ≠ F.branches.root j) :
    nearestMark F special j a = nearestMark F special j
      (TreePartition.parent (F.branches.isTree j) (F.branches.root j) haroot) := by
  rw [nearestMark.eq_def]
  simp [ha]

theorem nearestMark_mem (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) (j : Fin b)
    (a : Fin (F.branches.size j)) :
    (⟨j, nearestMark F special j a⟩ : BranchVertex F) ∈ marks F special := by
  classical
  induction hd : (F.branches.tree j).dist (F.branches.root j) a using
      Nat.strong_induction_on generalizing a with
  | h d ih =>
      by_cases ha : (⟨j, a⟩ : BranchVertex F) ∈ marks F special
      · rw [nearestMark_eq_self_of_mem F special j ha]
        exact ha
      · have haroot : a ≠ F.branches.root j := by
          intro hroot
          apply ha
          subst a
          exact branchRoot_mem_marks F special j
        let p := TreePartition.parent (F.branches.isTree j)
          (F.branches.root j) haroot
        have hpdist := TreePartition.parent_dist_add_one
          (F.branches.isTree j) (F.branches.root j) haroot
        have hpdist' :
            (F.branches.tree j).dist (F.branches.root j) p + 1 =
              (F.branches.tree j).dist (F.branches.root j) a := by
          simpa [p] using hpdist
        rw [nearestMark_eq_parent_of_not_mem F special j ha haroot]
        apply ih ((F.branches.tree j).dist (F.branches.root j) p)
        · omega
        · rfl

theorem nearestMark_dist_le (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) (j : Fin b)
    (a : Fin (F.branches.size j)) :
    (F.branches.tree j).dist (F.branches.root j)
        (nearestMark F special j a) ≤
      (F.branches.tree j).dist (F.branches.root j) a := by
  classical
  induction hd : (F.branches.tree j).dist (F.branches.root j) a using
      Nat.strong_induction_on generalizing a with
  | h d ih =>
      by_cases ha : (⟨j, a⟩ : BranchVertex F) ∈ marks F special
      · rw [nearestMark_eq_self_of_mem F special j ha]
        simpa [hd]
      · have haroot : a ≠ F.branches.root j := by
          intro hroot
          apply ha
          subst a
          exact branchRoot_mem_marks F special j
        let p := TreePartition.parent (F.branches.isTree j)
          (F.branches.root j) haroot
        have hpdist := TreePartition.parent_dist_add_one
          (F.branches.isTree j) (F.branches.root j) haroot
        have hpdist' :
            (F.branches.tree j).dist (F.branches.root j) p + 1 =
              (F.branches.tree j).dist (F.branches.root j) a := by
          simpa [p] using hpdist
        rw [nearestMark_eq_parent_of_not_mem F special j ha haroot]
        have hi := ih ((F.branches.tree j).dist (F.branches.root j) p)
          (by omega) p rfl
        calc
          (F.branches.tree j).dist (F.branches.root j)
              (nearestMark F special j
                (TreePartition.parent (F.branches.isTree j)
                  (F.branches.root j) haroot)) ≤
              (F.branches.tree j).dist (F.branches.root j) p := by
                simpa [p] using hi
          _ ≤ (F.branches.tree j).dist (F.branches.root j) a := by omega
          _ = d := hd

/-- A label which can change across a parent--child edge only at a marked
child is constant from every vertex to its nearest marked ancestor.  This is
the abstract invariant used to show that strengthened Zhao segments do not
mix matching-allocation classes. -/
theorem nearestMark_label_eq (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F))
    {κ : Type*}
    (label : (j : Fin b) → Fin (F.branches.size j) → κ)
    (hboundary : ∀ j a
      (haRoot : a ≠ F.branches.root j),
      label j (TreePartition.parent (F.branches.isTree j)
          (F.branches.root j) haRoot) ≠ label j a →
        (⟨j, a⟩ : BranchVertex F) ∈ marks F special)
    (j : Fin b) (a : Fin (F.branches.size j)) :
    label j (nearestMark F special j a) = label j a := by
  classical
  induction hd : (F.branches.tree j).dist (F.branches.root j) a using
      Nat.strong_induction_on generalizing a with
  | h d ih =>
      by_cases ha : (⟨j, a⟩ : BranchVertex F) ∈ marks F special
      · rw [nearestMark_eq_self_of_mem F special j ha]
      · have haRoot : a ≠ F.branches.root j := by
          intro hroot
          apply ha
          subst a
          exact branchRoot_mem_marks F special j
        let p := TreePartition.parent (F.branches.isTree j)
          (F.branches.root j) haRoot
        have hpdist := TreePartition.parent_dist_add_one
          (F.branches.isTree j) (F.branches.root j) haRoot
        have hpdist' :
            (F.branches.tree j).dist (F.branches.root j) p + 1 =
              (F.branches.tree j).dist (F.branches.root j) a := by
          simpa [p] using hpdist
        have hsame : label j p = label j a := by
          by_contra hne
          exact ha (hboundary j a haRoot (by simpa [p] using hne))
        rw [nearestMark_eq_parent_of_not_mem F special j ha haRoot]
        exact (ih ((F.branches.tree j).dist (F.branches.root j) p)
          (by omega) p rfl).trans hsame

theorem label_eq_mark_of_mem_fiber (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F))
    {κ : Type*}
    (label : (j : Fin b) → Fin (F.branches.size j) → κ)
    (hboundary : ∀ j a
      (haRoot : a ≠ F.branches.root j),
      label j (TreePartition.parent (F.branches.isTree j)
          (F.branches.root j) haRoot) ≠ label j a →
        (⟨j, a⟩ : BranchVertex F) ∈ marks F special)
    (q : BranchVertex F) (a : Fin (F.branches.size q.1))
    (ha : nearestMark F special q.1 a = q.2) :
    label q.1 a = label q.1 q.2 := by
  calc
    label q.1 a = label q.1 (nearestMark F special q.1 a) :=
      (nearestMark_label_eq F special label hboundary q.1 a).symm
    _ = label q.1 q.2 := congrArg (label q.1) ha

theorem nearestMark_parent_eq_of_fiber_of_ne
    (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) (j : Fin b)
    {q a : Fin (F.branches.size j)}
    (ha : nearestMark F special j a = q) (haq : a ≠ q) :
    ∃ haroot : a ≠ F.branches.root j,
      nearestMark F special j
        (TreePartition.parent (F.branches.isTree j) (F.branches.root j) haroot) = q := by
  have hanot : (⟨j, a⟩ : BranchVertex F) ∉ marks F special := by
    intro hamark
    apply haq
    rw [nearestMark_eq_self_of_mem F special j hamark] at ha
    exact ha
  have haroot : a ≠ F.branches.root j := by
    intro hroot
    apply hanot
    subst a
    exact branchRoot_mem_marks F special j
  refine ⟨haroot, ?_⟩
  rw [← nearestMark_eq_parent_of_not_mem F special j hanot haroot]
  exact ha

/-- The vertices in the segment rooted at a marked coordinate. -/
def fiberSet (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) (q : BranchVertex F) :
    Set (Fin (F.branches.size q.1)) :=
  {a | nearestMark F special q.1 a = q.2}

theorem mark_mem_fiberSet (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) {q : BranchVertex F}
    (hq : q ∈ marks F special) : q.2 ∈ fiberSet F special q := by
  exact nearestMark_eq_self_of_mem F special q.1 hq

/-- Every vertex of a fiber is joined to its marked root without leaving the
fiber, by repeatedly following the actual tree parent. -/
theorem fiber_reachable_mark (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) {q : BranchVertex F}
    (hq : q ∈ marks F special)
    (x : {a // a ∈ fiberSet F special q}) :
    ((F.branches.tree q.1).induce (fiberSet F special q)).Reachable x
      ⟨q.2, mark_mem_fiberSet F special hq⟩ := by
  classical
  induction hd : (F.branches.tree q.1).dist (F.branches.root q.1) x.1 using
      Nat.strong_induction_on generalizing x with
  | h d ih =>
      by_cases hxq : x.1 = q.2
      · have hxeq : x = ⟨q.2, mark_mem_fiberSet F special hq⟩ :=
          Subtype.ext hxq
        rw [hxeq]
      · obtain ⟨hxroot, hpFiber⟩ := nearestMark_parent_eq_of_fiber_of_ne
          F special q.1 x.2 hxq
        let p := TreePartition.parent (F.branches.isTree q.1)
          (F.branches.root q.1) hxroot
        let p' : {a // a ∈ fiberSet F special q} := ⟨p, hpFiber⟩
        have hpdist := TreePartition.parent_dist_add_one
          (F.branches.isTree q.1) (F.branches.root q.1) hxroot
        have hpdist' :
            (F.branches.tree q.1).dist (F.branches.root q.1) p + 1 =
              (F.branches.tree q.1).dist (F.branches.root q.1) x.1 := by
          simpa [p] using hpdist
        have hxp : ((F.branches.tree q.1).induce
            (fiberSet F special q)).Adj x p' := by
          change (F.branches.tree q.1).Adj x.1 p
          exact (TreePartition.parent_adj (F.branches.isTree q.1)
            (F.branches.root q.1) hxroot).symm
        exact hxp.reachable.trans
          (ih ((F.branches.tree q.1).dist (F.branches.root q.1) p)
            (by omega) p' rfl)

theorem fiberInduce_isTree (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) {q : BranchVertex F}
    (hq : q ∈ marks F special) :
    ((F.branches.tree q.1).induce (fiberSet F special q)).IsTree := by
  refine ⟨?_, (F.branches.isTree q.1).isAcyclic.induce _⟩
  let root : {a // a ∈ fiberSet F special q} :=
    ⟨q.2, mark_mem_fiberSet F special hq⟩
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨root, ?_⟩
  intro x
  exact (fiber_reachable_mark F special hq x).symm

/-! ## Distance-sorted marked fibers -/

def markKey (F : OrderedBranchForest r b) (z : BranchVertex F) : ℕ ×ₗ ℕ :=
  toLex ((F.branches.tree z.1).dist (F.branches.root z.1) z.2,
    (Fintype.equivFin (BranchVertex F) z).val)

theorem markKey_injective (F : OrderedBranchForest r b) :
    Function.Injective (markKey F) := by
  intro x y h
  have h' := toLex.injective h
  have hval : (Fintype.equivFin (BranchVertex F) x).val =
      (Fintype.equivFin (BranchVertex F) y).val := congrArg Prod.snd h'
  apply (Fintype.equivFin (BranchVertex F)).injective
  exact Fin.ext hval

def markLinearOrder (F : OrderedBranchForest r b) : LinearOrder (BranchVertex F) :=
  LinearOrder.lift' (markKey F) (markKey_injective F)

theorem lt_markLinearOrder_of_dist_lt (F : OrderedBranchForest r b)
    {x y : BranchVertex F}
    (hxy : (F.branches.tree x.1).dist (F.branches.root x.1) x.2 <
      (F.branches.tree y.1).dist (F.branches.root y.1) y.2) :
    @LT.lt (BranchVertex F) (markLinearOrder F).toLT x y := by
  change markKey F x < markKey F y
  rw [Prod.Lex.lt_iff]
  exact Or.inl hxy

noncomputable def markEnum (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) :
    Fin #(marks F special) ≃ {z // z ∈ marks F special} := by
  letI : LinearOrder (BranchVertex F) := markLinearOrder F
  exact ((marks F special).orderIsoOfFin rfl).toEquiv

noncomputable def markIndex (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) (z : BranchVertex F)
    (hz : z ∈ marks F special) : Fin #(marks F special) :=
  (markEnum F special).symm ⟨z, hz⟩

@[simp] theorem markEnum_index (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) (z : BranchVertex F)
    (hz : z ∈ marks F special) :
    (markEnum F special (markIndex F special z hz)).1 = z := by
  exact congrArg Subtype.val ((markEnum F special).apply_symm_apply ⟨z, hz⟩)

@[simp] theorem markIndex_enum (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) (i : Fin #(marks F special)) :
    markIndex F special (markEnum F special i).1 (markEnum F special i).2 = i := by
  exact (markEnum F special).symm_apply_apply i

theorem markIndex_lt_of_dist_lt (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F))
    {x y : BranchVertex F} (hx : x ∈ marks F special)
    (hy : y ∈ marks F special)
    (hxy : (F.branches.tree x.1).dist (F.branches.root x.1) x.2 <
      (F.branches.tree y.1).dist (F.branches.root y.1) y.2) :
    (markIndex F special x hx).val < (markIndex F special y hy).val := by
  let : LinearOrder (BranchVertex F) := markLinearOrder F
  let e : Fin #(marks F special) ≃o {z // z ∈ marks F special} :=
    (marks F special).orderIsoOfFin rfl
  have hsub : (⟨x, hx⟩ : {z // z ∈ marks F special}) < ⟨y, hy⟩ := by
    exact lt_markLinearOrder_of_dist_lt F hxy
  have hind : e.symm ⟨x, hx⟩ < e.symm ⟨y, hy⟩ := e.symm.lt_iff_lt.mpr hsub
  change e.symm ⟨x, hx⟩ < e.symm ⟨y, hy⟩
  exact hind

noncomputable def fiberEquiv (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) (i : Fin #(marks F special)) :
    Fin (Nat.card {a // a ∈ fiberSet F special (markEnum F special i).1}) ≃
      {a // a ∈ fiberSet F special (markEnum F special i).1} :=
  (Finite.equivFin _).symm

/-- The ordered forest of marked fibers.  Its component order refines source
depth, so the actual parent of every noninitial segment lies in an earlier
component. -/
noncomputable def segmentedOrderedForest (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) :
    OrderedRootedForest #(marks F special) where
  size i := Nat.card
    {a // a ∈ fiberSet F special (markEnum F special i).1}
  tree i := ((F.branches.tree (markEnum F special i).1.1).induce
      (fiberSet F special (markEnum F special i).1)).comap
        (fiberEquiv F special i)
  isTree i :=
    (SimpleGraph.Iso.comap (fiberEquiv F special i)
      ((F.branches.tree (markEnum F special i).1.1).induce
        (fiberSet F special (markEnum F special i).1))).isTree_iff.mpr
      (fiberInduce_isTree F special (markEnum F special i).2)
  root i := (fiberEquiv F special i).symm
    ⟨(markEnum F special i).1.2,
      mark_mem_fiberSet F special (markEnum F special i).2⟩

@[simp] theorem fiberEquiv_segmentedRoot (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) (i : Fin #(marks F special)) :
    fiberEquiv F special i ((segmentedOrderedForest F special).root i) =
      ⟨(markEnum F special i).1.2,
        mark_mem_fiberSet F special (markEnum F special i).2⟩ := by
  exact Equiv.apply_symm_apply _ _

/-- Transport a source coordinate into the canonically reindexed copy of the
fiber at a marked vertex. -/
noncomputable def fiberPointAtMark (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) (q : BranchVertex F)
    (hq : q ∈ marks F special) (a : Fin (F.branches.size q.1))
    (ha : a ∈ fiberSet F special q) :
    {x // x ∈ fiberSet F special
      (markEnum F special (markIndex F special q hq)).1} := by
  have henum := markEnum_index F special q hq
  exact henum.symm ▸ (⟨a, ha⟩ : {x // x ∈ fiberSet F special q})

theorem fiberPointAtMark_val_heq (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) (q : BranchVertex F)
    (hq : q ∈ marks F special) (a : Fin (F.branches.size q.1))
    (ha : a ∈ fiberSet F special q) :
    (fiberPointAtMark F special q hq a ha).1 ≍ a := by
  have hwhole : fiberPointAtMark F special q hq a ha ≍
      (⟨a, ha⟩ : {x // x ∈ fiberSet F special q}) := by
    unfold fiberPointAtMark
    apply eqRec_heq_self
  let e : BranchVertex F := (markEnum F special (markIndex F special q hq)).1
  have heq : e = q := markEnum_index F special q hq
  have hbase : Fin (F.branches.size e.1) = Fin (F.branches.size q.1) :=
    congrArg (fun z : BranchVertex F ↦ Fin (F.branches.size z.1)) heq
  have hpred : (fun x : Fin (F.branches.size e.1) ↦
      x ∈ fiberSet F special e) ≍
      (fun x : Fin (F.branches.size q.1) ↦ x ∈ fiberSet F special q) := by
    have hpack :
        (⟨Fin (F.branches.size e.1),
          fun x : Fin (F.branches.size e.1) ↦ x ∈ fiberSet F special e⟩ :
            Σ α : Type, α → Prop) =
        ⟨Fin (F.branches.size q.1),
          fun x : Fin (F.branches.size q.1) ↦ x ∈ fiberSet F special q⟩ :=
      congrArg (fun z : BranchVertex F ↦
        (⟨Fin (F.branches.size z.1),
          fun x : Fin (F.branches.size z.1) ↦ x ∈ fiberSet F special z⟩ :
            Σ α : Type, α → Prop)) heq
    exact (Sigma.mk.inj_iff.mp hpack).2
  exact (Subtype.heq_iff_coe_heq hbase hpred).mp hwhole

/-- Actual source parent of a marked segment.  Old branch roots attach to
their original A-layer owner; a newly exposed special root attaches to the
tree parent, represented in the fiber of that parent's nearest marked
ancestor. -/
noncomputable def segmentParent (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F))
    (i : Fin #(marks F special)) :
    Sum (Fin r) (Σ j, Fin ((segmentedOrderedForest F special).size j)) := by
  classical
  let q : BranchVertex F := (markEnum F special i).1
  if hroot : q.2 = F.branches.root q.1 then
    exact Sum.inl (F.owner q.1)
  else
    let p := TreePartition.parent (F.branches.isTree q.1)
      (F.branches.root q.1) hroot
    let pm : BranchVertex F := ⟨q.1, nearestMark F special q.1 p⟩
    have hpm : pm ∈ marks F special := nearestMark_mem F special q.1 p
    let k := markIndex F special pm hpm
    let pt := fiberPointAtMark F special pm hpm p (by rfl)
    exact Sum.inr ⟨k, (fiberEquiv F special k).symm pt⟩

theorem segmentParent_earlier (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F))
    (i j : Fin #(marks F special))
    (a : Fin ((segmentedOrderedForest F special).size j))
    (hparent : segmentParent F special i = Sum.inr ⟨j, a⟩) :
    j.val < i.val := by
  classical
  let q : BranchVertex F := (markEnum F special i).1
  by_cases hroot : q.2 = F.branches.root q.1
  · have hbad : (Sum.inl (F.owner q.1) :
        Sum (Fin r) (Σ j, Fin ((segmentedOrderedForest F special).size j))) =
          Sum.inr ⟨j, a⟩ := by
      simpa [segmentParent, q, hroot] using hparent
    cases hbad
  · let p := TreePartition.parent (F.branches.isTree q.1)
      (F.branches.root q.1) hroot
    let pm : BranchVertex F := ⟨q.1, nearestMark F special q.1 p⟩
    have hpm : pm ∈ marks F special := nearestMark_mem F special q.1 p
    let k := markIndex F special pm hpm
    have hjk : j = k := by
      have heq : (Sum.inr (Sigma.mk k
          ((fiberEquiv F special k).symm
            (fiberPointAtMark F special pm hpm p (by rfl)))) :
          Sum (Fin r) (Σ j, Fin ((segmentedOrderedForest F special).size j))) =
            Sum.inr ⟨j, a⟩ := by
        simpa [segmentParent, q, hroot, p, pm, hpm, k] using hparent
      exact (Sigma.mk.inj_iff.mp (Sum.inr.inj heq)).1.symm
    subst j
    have hdist : (F.branches.tree q.1).dist (F.branches.root q.1)
        (nearestMark F special q.1 p) <
        (F.branches.tree q.1).dist (F.branches.root q.1) q.2 := by
      have hnear := nearestMark_dist_le F special q.1 p
      have hpdist := TreePartition.parent_dist_add_one
        (F.branches.isTree q.1) (F.branches.root q.1) hroot
      have hpdist' : (F.branches.tree q.1).dist (F.branches.root q.1) p + 1 =
          (F.branches.tree q.1).dist (F.branches.root q.1) q.2 := by
        simpa [p] using hpdist
      omega
    have hlt := markIndex_lt_of_dist_lt F special hpm
      (markEnum F special i).2 hdist
    simpa [k, markIndex_enum] using hlt

/-- Canonical hierarchical segmentation at all old Level1 vertices and the
additional marked special vertices. -/
noncomputable def toHierarchicalSegmentForest
    (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) :
    HierarchicalSegmentForest r #(marks F special) where
  segments := segmentedOrderedForest F special
  parent := segmentParent F special
  parent_earlier := segmentParent_earlier F special

/-! ## Flattening back to the source branch forest -/

abbrev SegmentedVertex (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) :=
  (toHierarchicalSegmentForest F special).Vertex

/-- Forget the marked-fiber coordinate and recover the original branch
forest vertex. -/
noncomputable def flatten (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) :
    SegmentedVertex F special → F.Vertex
  | Sum.inl i => Sum.inl i
  | Sum.inr z =>
      let q := (markEnum F special z.1).1
      let a := (fiberEquiv F special z.1 z.2).1
      Sum.inr ⟨q.1, a⟩

/-- Send an original branch coordinate to the fiber of its nearest marked
ancestor. -/
noncomputable def unflatten (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) :
    F.Vertex → SegmentedVertex F special
  | Sum.inl i => Sum.inl i
  | Sum.inr z =>
      let q : BranchVertex F := ⟨z.1, nearestMark F special z.1 z.2⟩
      let hq : q ∈ marks F special := nearestMark_mem F special z.1 z.2
      let i := markIndex F special q hq
      let pt := fiberPointAtMark F special q hq z.2 (by rfl)
      Sum.inr ⟨i, (fiberEquiv F special i).symm pt⟩

theorem flatten_unflatten (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) (x : F.Vertex) :
    flatten F special (unflatten F special x) = x := by
  classical
  rcases x with i | z
  · rfl
  · rcases z with ⟨j, a⟩
    let q : BranchVertex F := ⟨j, nearestMark F special j a⟩
    let hq : q ∈ marks F special := nearestMark_mem F special j a
    let i := markIndex F special q hq
    let pt := fiberPointAtMark F special q hq a (by rfl)
    have henum := markEnum_index F special q hq
    have happly : fiberEquiv F special i
        ((fiberEquiv F special i).symm pt) = pt :=
      Equiv.apply_symm_apply _ _
    change Sum.inr (Sigma.mk (markEnum F special i).1.1
        (fiberEquiv F special i ((fiberEquiv F special i).symm pt)).1) =
      Sum.inr (Sigma.mk j a : BranchVertex F)
    rw [happly]
    apply congrArg Sum.inr
    apply Sigma.ext
    · simpa [i, q] using congrArg Sigma.fst henum
    · exact fiberPointAtMark_val_heq F special q hq a (by rfl)

def nearestMarkedVertex (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) (z : BranchVertex F) : BranchVertex F :=
  ⟨z.1, nearestMark F special z.1 z.2⟩

theorem nearestMarkedVertex_flatten_segment
    (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F))
    (i : Fin #(marks F special))
    (a : Fin ((segmentedOrderedForest F special).size i)) :
    nearestMarkedVertex F special
      ⟨(markEnum F special i).1.1, (fiberEquiv F special i a).1⟩ =
        (markEnum F special i).1 := by
  change (⟨(markEnum F special i).1.1,
    nearestMark F special (markEnum F special i).1.1
      (fiberEquiv F special i a).1⟩ : BranchVertex F) =
      (markEnum F special i).1
  exact Sigma.ext rfl (heq_of_eq (fiberEquiv F special i a).2)

theorem flatten_injective (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) :
    Function.Injective (flatten F special) := by
  classical
  rintro (i | z) (j | w) h
  · exact congrArg Sum.inl (Sum.inl.inj h)
  · change Sum.inl i = Sum.inr _ at h
    exact False.elim (Sum.inl_ne_inr h)
  · change Sum.inr _ = Sum.inl j at h
    exact False.elim (Sum.inr_ne_inl h)
  · rcases z with ⟨i, a⟩
    rcases w with ⟨j, c⟩
    have hbranch :
        (⟨(markEnum F special i).1.1, (fiberEquiv F special i a).1⟩ :
          BranchVertex F) =
        ⟨(markEnum F special j).1.1, (fiberEquiv F special j c).1⟩ :=
      Sum.inr.inj h
    have hmark := congrArg (nearestMarkedVertex F special) hbranch
    rw [nearestMarkedVertex_flatten_segment F special i a,
      nearestMarkedVertex_flatten_segment F special j c] at hmark
    have hij : i = j := by
      apply (markEnum F special).injective
      exact Subtype.ext hmark
    subst j
    have hval : (fiberEquiv F special i a).1 =
        (fiberEquiv F special i c).1 :=
      eq_of_heq (Sigma.mk.inj_iff.mp hbranch).2
    have hac : a = c := by
      apply (fiberEquiv F special i).injective
      exact Subtype.ext hval
    subst c
    rfl

theorem flatten_surjective (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) :
    Function.Surjective (flatten F special) := by
  intro x
  exact ⟨unflatten F special x, flatten_unflatten F special x⟩

/-- Canonical vertex equivalence between the segmented hierarchy and the
original ordered branch forest. -/
noncomputable def flattenEquiv (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) :
    SegmentedVertex F special ≃ F.Vertex :=
  Equiv.ofBijective (flatten F special)
    ⟨flatten_injective F special, flatten_surjective F special⟩

theorem sum_segmented_size (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) :
    (∑ i, (segmentedOrderedForest F special).size i) =
      ∑ j, F.branches.size j := by
  have hcard := Fintype.card_congr (flattenEquiv F special)
  change Fintype.card (Sum (Fin r)
      (Σ i, Fin ((segmentedOrderedForest F special).size i))) =
    Fintype.card (Sum (Fin r) (Σ j, Fin (F.branches.size j))) at hcard
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma] at hcard
  omega

theorem segmented_size_pos (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) (i : Fin #(marks F special)) :
    0 < (segmentedOrderedForest F special).size i := by
  have h := ((segmentedOrderedForest F special).root i).isLt
  omega

theorem branch_size_pos (F : OrderedBranchForest r b) (j : Fin b) :
    0 < F.branches.size j := by
  have h := (F.branches.root j).isLt
  omega

theorem segmented_deep_add_marks (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) :
    (∑ i, ((segmentedOrderedForest F special).size i - 1)) +
        #(marks F special) =
      ∑ i, (segmentedOrderedForest F special).size i := by
  calc
    (∑ i, ((segmentedOrderedForest F special).size i - 1)) +
        #(marks F special) =
        (∑ i, ((segmentedOrderedForest F special).size i - 1)) +
          ∑ _i : Fin #(marks F special), 1 := by simp
    _ = ∑ i, (((segmentedOrderedForest F special).size i - 1) + 1) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ i, (segmentedOrderedForest F special).size i := by
      apply Finset.sum_congr rfl
      intro i _
      exact Nat.sub_add_cancel (segmented_size_pos F special i)

theorem original_deep_add_branches (F : OrderedBranchForest r b) :
    (∑ j, (F.branches.size j - 1)) + b =
      ∑ j, F.branches.size j := by
  calc
    (∑ j, (F.branches.size j - 1)) + b =
        (∑ j, (F.branches.size j - 1)) + ∑ _j : Fin b, 1 := by simp
    _ = ∑ j, ((F.branches.size j - 1) + 1) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ j, F.branches.size j := by
      apply Finset.sum_congr rfl
      intro j _
      exact Nat.sub_add_cancel (branch_size_pos F j)

/-- Exposing special vertices only moves vertices from the matching layer to
the cluster-root layer; it never increases the total matching demand. -/
theorem segmented_deep_le_original (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) :
    (∑ i, ((segmentedOrderedForest F special).size i - 1)) ≤
      ∑ j, (F.branches.size j - 1) := by
  have hseg := segmented_deep_add_marks F special
  have horig := original_deep_add_branches F
  have htotal := sum_segmented_size F special
  have hroots := card_branchRoots_le_marks F special
  omega

@[simp] theorem flatten_segmentRoot (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) (i : Fin #(marks F special)) :
    flatten F special
      ((toHierarchicalSegmentForest F special).segmentRoot i) =
        Sum.inr (markEnum F special i).1 := by
  change Sum.inr (Sigma.mk (markEnum F special i).1.1
    (fiberEquiv F special i ((segmentedOrderedForest F special).root i)).1) =
      Sum.inr (markEnum F special i).1
  rw [fiberEquiv_segmentedRoot]

theorem unflatten_mark (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) (q : BranchVertex F)
    (hq : q ∈ marks F special) :
    unflatten F special (Sum.inr q) =
      (toHierarchicalSegmentForest F special).segmentRoot
        (markIndex F special q hq) := by
  apply flatten_injective F special
  rw [flatten_unflatten, flatten_segmentRoot]
  exact congrArg Sum.inr (markEnum_index F special q hq).symm

theorem exists_segmentRoot_unflatten_iff
    (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) (z : BranchVertex F) :
    (∃ i, unflatten F special (Sum.inr z) =
        (toHierarchicalSegmentForest F special).segmentRoot i) ↔
      z ∈ marks F special := by
  constructor
  · rintro ⟨i, hi⟩
    have hflat := congrArg (flatten F special) hi
    rw [flatten_unflatten, flatten_segmentRoot] at hflat
    have hz : z = (markEnum F special i).1 := Sum.inr.inj hflat
    rw [hz]
    exact (markEnum F special i).2
  · intro hz
    exact ⟨markIndex F special z hz, unflatten_mark F special z hz⟩

theorem unflatten_branchSpecial_is_segmentRoot
    (F : OrderedBranchForest r b) (special : Finset F.Vertex)
    (z : BranchVertex F) (hz : (Sum.inr z : F.Vertex) ∈ special) :
    ∃ i, unflatten F (branchSpecial F special) (Sum.inr z) =
      (toHierarchicalSegmentForest F (branchSpecial F special)).segmentRoot i := by
  apply (exists_segmentRoot_unflatten_iff F (branchSpecial F special) z).2
  exact special_subset_marks F (branchSpecial F special)
    ((mem_branchSpecial F special z).2 hz)

theorem unflatten_branchRoot_is_segmentRoot
    (F : OrderedBranchForest r b) (special : Finset (BranchVertex F))
    (j : Fin b) :
    ∃ i, unflatten F special
        (Sum.inr (⟨j, F.branches.root j⟩ : BranchVertex F)) =
      (toHierarchicalSegmentForest F special).segmentRoot i := by
  apply (exists_segmentRoot_unflatten_iff F special _).2
  exact branchRoot_mem_marks F special j

theorem flatten_segmentParent_of_not_root
    (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F))
    (i : Fin #(marks F special))
    (hroot : (markEnum F special i).1.2 ≠
      F.branches.root (markEnum F special i).1.1) :
    flatten F special ((toHierarchicalSegmentForest F special).parent i) =
      Sum.inr ⟨(markEnum F special i).1.1,
        TreePartition.parent
          (F.branches.isTree (markEnum F special i).1.1)
          (F.branches.root (markEnum F special i).1.1) hroot⟩ := by
  classical
  let q : BranchVertex F := (markEnum F special i).1
  let p := TreePartition.parent (F.branches.isTree q.1)
    (F.branches.root q.1) hroot
  let pm : BranchVertex F := ⟨q.1, nearestMark F special q.1 p⟩
  have hpm : pm ∈ marks F special := nearestMark_mem F special q.1 p
  let k := markIndex F special pm hpm
  let pt := fiberPointAtMark F special pm hpm p (by rfl)
  have happly : fiberEquiv F special k ((fiberEquiv F special k).symm pt) = pt :=
    Equiv.apply_symm_apply _ _
  change flatten F special (segmentParent F special i) = _
  rw [segmentParent]
  simp only [dif_neg hroot]
  change Sum.inr (Sigma.mk (markEnum F special k).1.1
      (fiberEquiv F special k ((fiberEquiv F special k).symm pt)).1) =
    Sum.inr (Sigma.mk q.1 p : BranchVertex F)
  rw [happly]
  apply congrArg Sum.inr
  apply Sigma.ext
  · simpa [k, pm] using congrArg Sigma.fst
      (markEnum_index F special pm hpm)
  · exact fiberPointAtMark_val_heq F special pm hpm p (by rfl)

theorem segmentParent_eq_unflatten_parent
    (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F))
    (i : Fin #(marks F special))
    (hroot : (markEnum F special i).1.2 ≠
      F.branches.root (markEnum F special i).1.1) :
    (toHierarchicalSegmentForest F special).parent i =
      unflatten F special (Sum.inr
        ⟨(markEnum F special i).1.1,
          TreePartition.parent
            (F.branches.isTree (markEnum F special i).1.1)
            (F.branches.root (markEnum F special i).1.1) hroot⟩) := by
  apply flatten_injective F special
  rw [flatten_segmentParent_of_not_root F special i hroot,
    flatten_unflatten]

theorem flatten_segmentPoint (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) (q : BranchVertex F)
    (hq : q ∈ marks F special) (a : Fin (F.branches.size q.1))
    (ha : a ∈ fiberSet F special q) :
    flatten F special
        (Sum.inr ⟨markIndex F special q hq,
          (fiberEquiv F special (markIndex F special q hq)).symm
            (fiberPointAtMark F special q hq a ha)⟩) =
      Sum.inr (⟨q.1, a⟩ : BranchVertex F) := by
  let i := markIndex F special q hq
  let pt := fiberPointAtMark F special q hq a ha
  have happly : fiberEquiv F special i ((fiberEquiv F special i).symm pt) = pt :=
    Equiv.apply_symm_apply _ _
  change Sum.inr (Sigma.mk (markEnum F special i).1.1
      (fiberEquiv F special i ((fiberEquiv F special i).symm pt)).1) =
    Sum.inr (Sigma.mk q.1 a : BranchVertex F)
  rw [happly]
  apply congrArg Sum.inr
  apply Sigma.ext
  · simpa [i] using congrArg Sigma.fst (markEnum_index F special q hq)
  · exact fiberPointAtMark_val_heq F special q hq a ha

theorem unflatten_segmentPoint (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) (q : BranchVertex F)
    (hq : q ∈ marks F special) (a : Fin (F.branches.size q.1))
    (ha : a ∈ fiberSet F special q) :
    unflatten F special (Sum.inr (⟨q.1, a⟩ : BranchVertex F)) =
      Sum.inr ⟨markIndex F special q hq,
        (fiberEquiv F special (markIndex F special q hq)).symm
          (fiberPointAtMark F special q hq a ha)⟩ := by
  apply flatten_injective F special
  rw [flatten_unflatten, flatten_segmentPoint]

/-- Adjacent coordinates with the same nearest marked ancestor become an
internal edge of one segment. -/
theorem graph_adj_unflatten_of_same_fiber (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) (j : Fin b)
    {a c : Fin (F.branches.size j)}
    (hsame : nearestMark F special j a = nearestMark F special j c)
    (hadj : (F.branches.tree j).Adj a c) :
    (toHierarchicalSegmentForest F special).graph.Adj
      (unflatten F special (Sum.inr (⟨j, a⟩ : BranchVertex F)))
      (unflatten F special (Sum.inr (⟨j, c⟩ : BranchVertex F))) := by
  let q : BranchVertex F := ⟨j, nearestMark F special j a⟩
  have hq : q ∈ marks F special := nearestMark_mem F special j a
  have ha : a ∈ fiberSet F special q := rfl
  have hc : c ∈ fiberSet F special q := hsame.symm
  rw [unflatten_segmentPoint F special q hq a ha,
    unflatten_segmentPoint F special q hq c hc]
  left
  refine ⟨markIndex F special q hq,
    (fiberEquiv F special (markIndex F special q hq)).symm
      (fiberPointAtMark F special q hq a ha),
    (fiberEquiv F special (markIndex F special q hq)).symm
      (fiberPointAtMark F special q hq c hc), rfl, rfl, ?_⟩
  simp only [toHierarchicalSegmentForest, segmentedOrderedForest,
    SimpleGraph.comap_adj, SimpleGraph.induce_adj]
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  convert hadj using 1
  · exact congrArg (fun k ↦ Fin (F.branches.size k)) (by
      simpa [q] using congrArg Sigma.fst (markEnum_index F special q hq))
  · let k := (markEnum F special (markIndex F special q hq)).1.1
    have hkj : k = j := by
      simpa [k, q] using congrArg Sigma.fst (markEnum_index F special q hq)
    have hpack := congrArg
      (fun l ↦ (⟨l, F.branches.tree l⟩ :
        Σ n, SimpleGraph (Fin (F.branches.size n)))) hkj
    exact (Sigma.mk.inj_iff.mp hpack).2
  · exact fiberPointAtMark_val_heq F special q hq a ha
  · exact fiberPointAtMark_val_heq F special q hq c hc

theorem segmentParent_branchRoot (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) (j : Fin b) :
    (toHierarchicalSegmentForest F special).parent
        (markIndex F special
          (⟨j, F.branches.root j⟩ : BranchVertex F)
          (branchRoot_mem_marks F special j)) =
      Sum.inl (F.owner j) := by
  change segmentParent F special
      (markIndex F special
        (⟨j, F.branches.root j⟩ : BranchVertex F)
        (branchRoot_mem_marks F special j)) = _
  let q : BranchVertex F := ⟨j, F.branches.root j⟩
  let hq : q ∈ marks F special := branchRoot_mem_marks F special j
  let i := markIndex F special q hq
  have henum : (markEnum F special i).1 = q :=
    markEnum_index F special q hq
  have hroot : (markEnum F special i).1.2 =
      F.branches.root (markEnum F special i).1.1 := by
    rw [henum]
  change segmentParent F special i = _
  rw [segmentParent]
  simp only [dif_pos hroot]
  exact congrArg Sum.inl (congrArg F.owner (congrArg Sigma.fst henum))

/-- Each oriented parent--child edge is either internal to one marked fiber,
or is exactly the attachment edge of the child segment. -/
theorem graph_adj_unflatten_parent_child (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) (j : Fin b)
    {a : Fin (F.branches.size j)} (haRoot : a ≠ F.branches.root j) :
    (toHierarchicalSegmentForest F special).graph.Adj
      (unflatten F special (Sum.inr
        (⟨j, TreePartition.parent (F.branches.isTree j)
          (F.branches.root j) haRoot⟩ : BranchVertex F)))
      (unflatten F special (Sum.inr (⟨j, a⟩ : BranchVertex F))) := by
  classical
  by_cases haMark : (⟨j, a⟩ : BranchVertex F) ∈ marks F special
  · let q : BranchVertex F := ⟨j, a⟩
    let i := markIndex F special q haMark
    have henum : (markEnum F special i).1 = q :=
      markEnum_index F special q haMark
    have hiRoot : (markEnum F special i).1.2 ≠
        F.branches.root (markEnum F special i).1.1 := by
      rw [henum]
      exact haRoot
    have hp : (toHierarchicalSegmentForest F special).parent i =
        unflatten F special (Sum.inr
          (⟨j, TreePartition.parent (F.branches.isTree j)
            (F.branches.root j) haRoot⟩ : BranchVertex F)) := by
      have hp' := segmentParent_eq_unflatten_parent F special i hiRoot
      let SourceNonroot :=
        {z : BranchVertex F // z.2 ≠ F.branches.root z.1}
      let e : SourceNonroot := ⟨(markEnum F special i).1, hiRoot⟩
      let z : SourceNonroot := ⟨q, haRoot⟩
      have hez : e = z := Subtype.ext henum
      let parentCoordinate : SourceNonroot → BranchVertex F := fun w ↦
        ⟨w.1.1, TreePartition.parent (F.branches.isTree w.1.1)
          (F.branches.root w.1.1) w.2⟩
      have hparentCoordinate : parentCoordinate e = parentCoordinate z :=
        congrArg parentCoordinate hez
      calc
        (toHierarchicalSegmentForest F special).parent i =
            unflatten F special (Sum.inr (parentCoordinate e)) := hp'
        _ = unflatten F special (Sum.inr (parentCoordinate z)) := by
          rw [hparentCoordinate]
        _ = unflatten F special (Sum.inr
            (⟨j, TreePartition.parent (F.branches.isTree j)
              (F.branches.root j) haRoot⟩ : BranchVertex F)) := rfl
    have hr : unflatten F special (Sum.inr (⟨j, a⟩ : BranchVertex F)) =
        (toHierarchicalSegmentForest F special).segmentRoot i := by
      simpa [i, q] using unflatten_mark F special q haMark
    rw [← hp, hr]
    exact Or.inr (Or.inl ⟨i, rfl, rfl⟩)
  · have hnear := nearestMark_eq_parent_of_not_mem F special j haMark haRoot
    exact graph_adj_unflatten_of_same_fiber F special j hnear.symm
      (TreePartition.parent_adj (F.branches.isTree j)
        (F.branches.root j) haRoot)

/-- The inverse of `flatten` is a graph homomorphism from the original
branch forest into the reconstructed hierarchical graph. -/
theorem graph_adj_unflatten (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) {x y : F.Vertex}
    (hxy : F.graph.Adj x y) :
    (toHierarchicalSegmentForest F special).graph.Adj
      (unflatten F special x) (unflatten F special y) := by
  classical
  rcases x with i | z <;> rcases y with k | w
  · exact False.elim hxy
  · rcases hxy with ⟨hown, hroot⟩
    subst i
    rcases w with ⟨j, a⟩
    dsimp only at hroot
    subst a
    have hr := unflatten_mark F special
      (⟨j, F.branches.root j⟩ : BranchVertex F)
      (branchRoot_mem_marks F special j)
    rw [hr]
    exact Or.inr (Or.inl ⟨_, by
      simp [unflatten, segmentParent_branchRoot], rfl⟩)
  · rcases hxy with ⟨hown, hroot⟩
    subst k
    rcases z with ⟨j, a⟩
    dsimp only at hroot
    subst a
    have hr := unflatten_mark F special
      (⟨j, F.branches.root j⟩ : BranchVertex F)
      (branchRoot_mem_marks F special j)
    rw [hr]
    exact Or.inr (Or.inr ⟨_, by
      simp [unflatten, segmentParent_branchRoot], rfl⟩)
  · rcases hxy with ⟨hjk, hadj⟩
    rcases z with ⟨j, a⟩
    rcases w with ⟨k, c⟩
    dsimp only at hjk
    subst k
    rcases (F.branches.isTree j).dist_eq_dist_add_one_of_adj
        (F.branches.root j) hadj with hlevel | hlevel
    · have haRoot : a ≠ F.branches.root j := by
        intro ha
        subst a
        simp at hlevel
      have hcParent : c = TreePartition.parent (F.branches.isTree j)
          (F.branches.root j) haRoot :=
        TreePartition.eq_parent_of_adj_of_dist_add_one
          (F.branches.isTree j) (F.branches.root j) haRoot hadj.symm hlevel.symm
      subst c
      exact (graph_adj_unflatten_parent_child F special j haRoot).symm
    · have hcRoot : c ≠ F.branches.root j := by
        intro hc
        subst c
        simp at hlevel
      have haParent : a = TreePartition.parent (F.branches.isTree j)
          (F.branches.root j) hcRoot :=
        TreePartition.eq_parent_of_adj_of_dist_add_one
          (F.branches.isTree j) (F.branches.root j) hcRoot hadj hlevel.symm
      subst a
      exact graph_adj_unflatten_parent_child F special j hcRoot

/-- A concrete copy of the hierarchy transports back to a concrete copy of
the original ordered branch forest; there is no copy or adjacency premise in
the segmentation itself. -/
def copyOfHierarchicalCopy
    {B : Type u} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (special : Finset (BranchVertex F))
    (G : SimpleGraph B)
    (C : (toHierarchicalSegmentForest F special).graph.Copy G) :
    F.graph.Copy G where
  toHom :=
    { toFun := fun x ↦ C.toHom (unflatten F special x)
      map_rel' := by
        intro x y hxy
        exact C.toHom.map_rel (graph_adj_unflatten F special hxy) }
  injective' := by
    intro x y hxy
    have hu : unflatten F special x = unflatten F special y := C.injective hxy
    calc
      x = flatten F special (unflatten F special x) :=
        (flatten_unflatten F special x).symm
      _ = flatten F special (unflatten F special y) := congrArg _ hu
      _ = y := flatten_unflatten F special y

@[simp] theorem copyOfHierarchicalCopy_apply
    {B : Type u} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (special : Finset (BranchVertex F))
    (G : SimpleGraph B)
    (C : (toHierarchicalSegmentForest F special).graph.Copy G)
    (x : F.Vertex) :
    copyOfHierarchicalCopy F special G C x =
      C (unflatten F special x) := rfl

/-- Layer-preserving transport from a realized hierarchy to Zhao's original
three-layer source object.  Oddness is used only to rule out an original
root from the optional special set. -/
def threeLayerCopyOfHierarchicalCopy
    {B : Type u} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B)
    (rootImage : Fin r → B) (special : Finset F.Vertex)
    (clusterTarget matchingTarget : Finset B)
    (hspecialOdd : special ⊆ F.oddVertices)
    (C : (toHierarchicalSegmentForest F (branchSpecial F special)).graph.Copy G)
    (hroot : ∀ i, C (Sum.inl i) = rootImage i)
    (hsegmentRoot : ∀ i,
      C ((toHierarchicalSegmentForest F (branchSpecial F special)).segmentRoot i) ∈
        clusterTarget)
    (hsegmentNonroot : ∀ i a,
      a ≠ (segmentedOrderedForest F (branchSpecial F special)).root i →
      C (Sum.inr ⟨i, a⟩) ∈ matchingTarget) :
    ThreeLayerCopy F G rootImage special clusterTarget matchingTarget := by
  classical
  let sourceSpecial := branchSpecial F special
  let H := toHierarchicalSegmentForest F sourceSpecial
  let copy := copyOfHierarchicalCopy F sourceSpecial G C
  refine
    { copy := copy
      map_root := ?_
      map_levelOne := ?_
      map_special := ?_
      map_remaining := ?_ }
  · intro i
    change C (unflatten F sourceSpecial (Sum.inl i)) = rootImage i
    exact hroot i
  · intro x hx
    obtain ⟨j, rfl⟩ := (F.mem_levelOne_iff x).mp hx
    obtain ⟨i, hi⟩ := unflatten_branchRoot_is_segmentRoot F sourceSpecial j
    change C (unflatten F sourceSpecial
      (Sum.inr (Sigma.mk j (F.branches.root j)))) ∈ clusterTarget
    rw [hi]
    exact hsegmentRoot i
  · intro x hx
    rcases x with i | z
    · have hodd := hspecialOdd hx
      simp [OrderedBranchForest.oddVertices] at hodd
    · obtain ⟨i, hi⟩ := unflatten_branchSpecial_is_segmentRoot F special z hx
      change C (unflatten F sourceSpecial (Sum.inr z)) ∈ clusterTarget
      rw [hi]
      exact hsegmentRoot i
  · intro x hnotRoot hnotLevelOne hnotSpecial
    rcases x with i | z
    · exfalso
      apply hnotRoot
      exact (F.mem_roots_iff (Sum.inl i)).2 ⟨i, rfl⟩
    · cases hU : unflatten F sourceSpecial (Sum.inr z) with
      | inl q =>
          have hflat := congrArg (flatten F sourceSpecial) hU
          rw [flatten_unflatten] at hflat
          exact False.elim (Sum.inr_ne_inl hflat)
      | inr w =>
          have hw : w.2 ≠
              (segmentedOrderedForest F sourceSpecial).root w.1 := by
            intro hw
            have hseg : ∃ i, unflatten F sourceSpecial (Sum.inr z) =
                H.segmentRoot i := by
              refine ⟨w.1, ?_⟩
              rw [hU]
              change Sum.inr w = Sum.inr
                ⟨w.1, (segmentedOrderedForest F sourceSpecial).root w.1⟩
              exact congrArg Sum.inr (Sigma.ext rfl (heq_of_eq hw))
            have hzmark :=
              (exists_segmentRoot_unflatten_iff F sourceSpecial z).mp hseg
            rcases Finset.mem_union.mp hzmark with hzroot | hzspecial
            · obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hzroot
              have hz : z =
                  (⟨j, F.branches.root j⟩ : BranchVertex F) := hj.symm
              subst z
              exact hnotLevelOne
                ((F.mem_levelOne_iff _).2 ⟨j, rfl⟩)
            · exact hnotSpecial ((mem_branchSpecial F special z).mp hzspecial)
          change C (unflatten F sourceSpecial (Sum.inr z)) ∈ matchingTarget
          rw [hU]
          exact hsegmentNonroot w.1 w.2 hw

end Erdos547b.ZhaoLemma59SpecialSegmentation

#print axioms Erdos547b.ZhaoLemma59SpecialSegmentation.fiberInduce_isTree
#print axioms Erdos547b.ZhaoLemma59SpecialSegmentation.copyOfHierarchicalCopy
#print axioms Erdos547b.ZhaoLemma59SpecialSegmentation.threeLayerCopyOfHierarchicalCopy
