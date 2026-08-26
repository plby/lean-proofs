/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58GroupedSmallForest
import ErdosProblems.Erdos547b.ForestMatching
import ErdosProblems.Erdos547b.Claim616SourceBridge

/-!
# Same-edge state threading for Zhao Lemma 5.8

Part 3 of Zhao Lemma 5.4 is applied separately below each already embedded
outer root.  Several such owner-coherent batches may nevertheless use the
same matching edge.  They cannot be assembled as independent embeddings,
because their two endpoint supports overlap.  Instead the batches are
processed sequentially: the exact image of every completed batch is removed
from the two live endpoint sets before the next batch is realized.

This file supplies that graph-theoretic state transition.  It is independent
of the Part-1/2/3 numerical arguments.  The low-level `appendPartial` is an
internal composition lemma and therefore takes the two already realized
batch embeddings.  The public owner-batch theorem below constructs those
records recursively from a local realization theorem in the exact residual
sets; `appendPartial` is not a final Lemma-5.8 endpoint.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma58DynamicBatchAppend

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ForestMatching
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoClaim616SourceBridge

universe v

/-- An attached embedding of a literal selected subfamily of an ordered
forest.  Unlike `DynamicAttachedForestEmbedding`, component indices remain
the original `Fin b` indices; this makes unions of owner batches literal. -/
structure PartialDynamicAttachedForestEmbedding
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B)
    (externalParent : Fin b → B)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (available : Fin 2 → Finset B)
    (selected : Finset (Fin b)) where
  forestCopy : OrderedForestCopy selected
    (fun i ↦ Fin (F.size i)) (fun i ↦ F.tree i) G
  attach : ∀ i (hi : i ∈ selected),
    G.Adj (externalParent i)
      (forestCopy.componentCopy i hi (F.root i))
  map_side : ∀ i (hi : i ∈ selected) a,
    forestCopy.componentCopy i hi a ∈
      available (orient i
        ((F.isTree i).coloringTwoOfVert (F.root i) a))

/-! ### Literal reindexing of one selected batch -/

/-- The ordered rooted forest obtained by retaining exactly the components
in `selected`, in the canonical finset order.  This is the branch-only
analogue of `OrderedBranchForest.restrict`; it is used while one matching
edge is processed owner by owner. -/
noncomputable def selectedForest {b : ℕ} (F : OrderedRootedForest b)
    (selected : Finset (Fin b)) : OrderedRootedForest selected.card where
  size i := F.size
    (OrderedBranchForest.selectedEquiv selected i)
  tree i := F.tree
    (OrderedBranchForest.selectedEquiv selected i)
  isTree i := F.isTree
    (OrderedBranchForest.selectedEquiv selected i)
  root i := F.root
    (OrderedBranchForest.selectedEquiv selected i)

@[simp] theorem selectedForest_size {b : ℕ} (F : OrderedRootedForest b)
    (selected : Finset (Fin b)) (i : Fin selected.card) :
    (selectedForest F selected).size i =
      F.size (OrderedBranchForest.selectedEquiv selected i) := rfl

@[simp] theorem selectedForest_tree {b : ℕ} (F : OrderedRootedForest b)
    (selected : Finset (Fin b)) (i : Fin selected.card) :
    (selectedForest F selected).tree i =
      F.tree (OrderedBranchForest.selectedEquiv selected i) := rfl

/-- Coordinate of an original selected component in the canonical selected
forest. -/
noncomputable def selectedIndex {b : ℕ} (selected : Finset (Fin b))
    (i : Fin b) (hi : i ∈ selected) : Fin selected.card :=
  (OrderedBranchForest.selectedEquiv selected).symm ⟨i, hi⟩

@[simp] theorem selectedEquiv_selectedIndex {b : ℕ}
    (selected : Finset (Fin b)) (i : Fin b) (hi : i ∈ selected) :
    ((OrderedBranchForest.selectedEquiv selected
      (selectedIndex selected i hi) : {j // j ∈ selected}) : Fin b) = i := by
  simp [selectedIndex]

/-- Vertex coordinate transported to the selected-family copy. -/
noncomputable def selectedVertex {b : ℕ} (F : OrderedRootedForest b)
    (selected : Finset (Fin b)) (i : Fin b) (hi : i ∈ selected)
    (a : Fin (F.size i)) :
    Fin ((selectedForest F selected).size
      (selectedIndex selected i hi)) :=
  Fin.cast (by
    simp only [selectedForest_size, selectedEquiv_selectedIndex]) a

@[simp] theorem selectedVertex_val {b : ℕ} (F : OrderedRootedForest b)
    (selected : Finset (Fin b)) (i : Fin b) (hi : i ∈ selected)
    (a : Fin (F.size i)) :
    (selectedVertex F selected i hi a).val = a.val := by
  rfl

theorem selectedVertex_injective {b : ℕ} (F : OrderedRootedForest b)
    (selected : Finset (Fin b)) (i : Fin b) (hi : i ∈ selected) :
    Function.Injective (selectedVertex F selected i hi) := by
  intro a d had
  apply Fin.ext
  simpa using congrArg Fin.val had

private theorem tree_adj_cast_index {b : ℕ} (F : OrderedRootedForest b)
    {i j : Fin b} (hji : j = i) (a d : Fin (F.size i))
    (had : (F.tree i).Adj a d) :
    (F.tree j).Adj
      (Fin.cast (congrArg F.size hji.symm) a)
      (Fin.cast (congrArg F.size hji.symm) d) := by
  subst j
  simpa using had

private theorem root_cast_index {b : ℕ} (F : OrderedRootedForest b)
    {i j : Fin b} (hji : j = i) :
    F.root j = Fin.cast (congrArg F.size hji.symm) (F.root i) := by
  subst j
  rfl

@[simp] theorem selectedVertex_root {b : ℕ} (F : OrderedRootedForest b)
    (selected : Finset (Fin b)) (i : Fin b) (hi : i ∈ selected) :
    selectedVertex F selected i hi (F.root i) =
      (selectedForest F selected).root (selectedIndex selected i hi) := by
  have hidx := selectedEquiv_selectedIndex selected i hi
  apply Fin.ext
  change (F.root i).val =
    (F.root (OrderedBranchForest.selectedEquiv selected
      (selectedIndex selected i hi))).val
  exact (congrArg (fun k ↦ (F.root k).val) hidx).symm

private theorem coloring_cast_index {b : ℕ} (F : OrderedRootedForest b)
    {i j : Fin b} (hji : j = i) (a : Fin (F.size i)) :
    (F.isTree j).coloringTwoOfVert (F.root j)
        (Fin.cast (congrArg F.size hji.symm) a) =
      (F.isTree i).coloringTwoOfVert (F.root i) a := by
  subst j
  rfl

/-- The canonical selected-family vertex preserves the rooted two-colouring
of its original component. -/
@[simp] theorem selectedVertex_coloring {b : ℕ} (F : OrderedRootedForest b)
    (selected : Finset (Fin b)) (i : Fin b) (hi : i ∈ selected)
    (a : Fin (F.size i)) :
    ((selectedForest F selected).isTree (selectedIndex selected i hi)
      |>.coloringTwoOfVert
        ((selectedForest F selected).root (selectedIndex selected i hi))
        (selectedVertex F selected i hi a)) =
      (F.isTree i).coloringTwoOfVert (F.root i) a := by
  have hidx := selectedEquiv_selectedIndex selected i hi
  have ha : selectedVertex F selected i hi a =
      Fin.cast (congrArg F.size hidx.symm) a := by
    apply Fin.ext
    rfl
  change (F.isTree
      (OrderedBranchForest.selectedEquiv selected
        (selectedIndex selected i hi))).coloringTwoOfVert
      (F.root (OrderedBranchForest.selectedEquiv selected
        (selectedIndex selected i hi)))
      (selectedVertex F selected i hi a) = _
  rw [ha]
  exact coloring_cast_index F hidx a

/-- Pull the concrete copy of one selected-family component back to its
literal original component. -/
noncomputable def selectedComponentCopy
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B)
    (externalParent : Fin b → B)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (available : Fin 2 → Finset B) (selected : Finset (Fin b))
    (E : DynamicAttachedForestEmbedding (selectedForest F selected) G
      (fun k ↦ externalParent
        (OrderedBranchForest.selectedEquiv selected k))
      (fun k ↦ orient (OrderedBranchForest.selectedEquiv selected k))
      available)
    (i : Fin b) (hi : i ∈ selected) : (F.tree i).Copy G where
  toHom := {
    toFun := fun a ↦ E.embedding.copy (selectedIndex selected i hi)
      (selectedVertex F selected i hi a)
    map_rel' := by
      intro a d had
      apply (E.embedding.copy (selectedIndex selected i hi)).toHom.map_rel
      have hidx := selectedEquiv_selectedIndex selected i hi
      simpa only [selectedForest_tree, selectedForest_size, selectedVertex] using
        tree_adj_cast_index F hidx a d had
  }
  injective' :=
    (E.embedding.copy (selectedIndex selected i hi)).injective.comp
      (selectedVertex_injective F selected i hi)

@[simp] theorem selectedComponentCopy_apply
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B)
    (externalParent : Fin b → B)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (available : Fin 2 → Finset B) (selected : Finset (Fin b))
    (E : DynamicAttachedForestEmbedding (selectedForest F selected) G
      (fun k ↦ externalParent
        (OrderedBranchForest.selectedEquiv selected k))
      (fun k ↦ orient (OrderedBranchForest.selectedEquiv selected k))
      available)
    (i : Fin b) (hi : i ∈ selected) (a : Fin (F.size i)) :
    selectedComponentCopy F G externalParent orient available selected E i hi a =
      E.embedding.copy (selectedIndex selected i hi)
        (selectedVertex F selected i hi a) := rfl

/-- Reindex a dynamic embedding of a selected family back to the literal
original component indices. -/
noncomputable def partialOfSelectedForest
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B)
    (externalParent : Fin b → B)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (available : Fin 2 → Finset B) (selected : Finset (Fin b))
    (E : DynamicAttachedForestEmbedding (selectedForest F selected) G
      (fun k ↦ externalParent
        (OrderedBranchForest.selectedEquiv selected k))
      (fun k ↦ orient (OrderedBranchForest.selectedEquiv selected k))
      available) :
    PartialDynamicAttachedForestEmbedding
      F G externalParent orient available selected where
  forestCopy := {
    componentCopy := selectedComponentCopy F G externalParent orient
      available selected E
    disjoint_ranges := by
      intro i hi j hj hij
      rw [Set.disjoint_left]
      intro z hzi hzj
      obtain ⟨a, ha⟩ := hzi
      obtain ⟨d, hd⟩ := hzj
      have hcopy :
          E.embedding.copy (selectedIndex selected i hi)
              (selectedVertex F selected i hi a) =
            E.embedding.copy (selectedIndex selected j hj)
              (selectedVertex F selected j hj d) := by
        simpa only [selectedComponentCopy_apply] using ha.trans hd.symm
      have hsigma :
          (⟨selectedIndex selected i hi,
              selectedVertex F selected i hi a⟩ :
            Σ k, Fin ((selectedForest F selected).size k)) =
          ⟨selectedIndex selected j hj,
              selectedVertex F selected j hj d⟩ :=
        E.embedding.injective hcopy
      have hindex : selectedIndex selected i hi =
          selectedIndex selected j hj := congrArg Sigma.fst hsigma
      apply hij
      have horiginal := congrArg (fun k ↦
        ((OrderedBranchForest.selectedEquiv selected k :
          {x // x ∈ selected}) : Fin b)) hindex
      simpa only [selectedEquiv_selectedIndex] using horiginal
  }
  attach := by
    intro i hi
    have hidx := selectedEquiv_selectedIndex selected i hi
    have ha := E.attach (selectedIndex selected i hi)
    change G.Adj (externalParent (OrderedBranchForest.selectedEquiv selected
        (selectedIndex selected i hi)))
      (E.embedding.copy (selectedIndex selected i hi)
        ((selectedForest F selected).root
          (selectedIndex selected i hi))) at ha
    have hparent := congrArg externalParent hidx
    rw [hparent] at ha
    simpa only [selectedComponentCopy_apply, selectedVertex_root] using ha
  map_side := by
    intro i hi a
    have hidx := selectedEquiv_selectedIndex selected i hi
    have hm := E.map_side (selectedIndex selected i hi)
      (selectedVertex F selected i hi a)
    change E.embedding.copy (selectedIndex selected i hi)
        (selectedVertex F selected i hi a) ∈
      available (orient (OrderedBranchForest.selectedEquiv selected
        (selectedIndex selected i hi))
        ((F.isTree (OrderedBranchForest.selectedEquiv selected
          (selectedIndex selected i hi))).coloringTwoOfVert
          (F.root (OrderedBranchForest.selectedEquiv selected
            (selectedIndex selected i hi)))
          (selectedVertex F selected i hi a))) at hm
    have hvertex : selectedVertex F selected i hi a =
        Fin.cast (congrArg F.size hidx.symm) a := by
      apply Fin.ext
      rfl
    have horient := congrArg orient hidx
    have hcolor :
        (F.isTree (OrderedBranchForest.selectedEquiv selected
          (selectedIndex selected i hi))).coloringTwoOfVert
            (F.root (OrderedBranchForest.selectedEquiv selected
              (selectedIndex selected i hi)))
            (selectedVertex F selected i hi a) =
          (F.isTree i).coloringTwoOfVert (F.root i) a := by
      rw [hvertex]
      exact coloring_cast_index F hidx a
    rw [horient, hcolor] at hm
    simpa only [selectedComponentCopy_apply] using hm

/-- Exact vertices used by a partial embedding on physical side `c`. -/
def PartialDynamicAttachedForestEmbedding.used
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    {F : OrderedRootedForest b} {G : SimpleGraph B}
    {externalParent : Fin b → B}
    {orient : Fin b → Fin 2 ≃ Fin 2}
    {available : Fin 2 → Finset B} {selected : Finset (Fin b)}
    (E : PartialDynamicAttachedForestEmbedding
      F G externalParent orient available selected)
    (c : Fin 2) : Finset B :=
  Finset.univ.biUnion fun i : {i // i ∈ selected} ↦
    orientedCopyImage (F.tree i.1) (F.isTree i.1) (F.root i.1)
      (orient i.1) G (E.forestCopy.componentCopy i.1 i.2) c

theorem PartialDynamicAttachedForestEmbedding.copy_mem_used
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    {F : OrderedRootedForest b} {G : SimpleGraph B}
    {externalParent : Fin b → B}
    {orient : Fin b → Fin 2 ≃ Fin 2}
    {available : Fin 2 → Finset B} {selected : Finset (Fin b)}
    (E : PartialDynamicAttachedForestEmbedding
      F G externalParent orient available selected)
    (i : Fin b) (hi : i ∈ selected) (a : Fin (F.size i)) :
    E.forestCopy.componentCopy i hi a ∈
      E.used (orient i ((F.isTree i).coloringTwoOfVert (F.root i) a)) := by
  apply Finset.mem_biUnion.mpr
  refine ⟨⟨i, hi⟩, Finset.mem_univ _, ?_⟩
  exact copy_mem_orientedCopyImage (F.tree i) (F.isTree i) (F.root i)
    (orient i) G (E.forestCopy.componentCopy i hi) a

theorem PartialDynamicAttachedForestEmbedding.used_subset
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    {F : OrderedRootedForest b} {G : SimpleGraph B}
    {externalParent : Fin b → B}
    {orient : Fin b → Fin 2 ≃ Fin 2}
    {available : Fin 2 → Finset B} {selected : Finset (Fin b)}
    (E : PartialDynamicAttachedForestEmbedding
      F G externalParent orient available selected)
    (c : Fin 2) : E.used c ⊆ available c := by
  intro x hx
  obtain ⟨i, _hi, hxi⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hxi
  have hside := (Finset.mem_filter.mp ha).2
  simpa only [hside] using E.map_side i.1 i.2 a

/-- The empty initial state for same-edge owner batching. -/
noncomputable def emptyPartial
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B)
    (externalParent : Fin b → B)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (available : Fin 2 → Finset B) :
    PartialDynamicAttachedForestEmbedding
      F G externalParent orient available ∅ where
  forestCopy := {
    componentCopy := by
      intro i hi
      have : False := by simpa using hi
      exact False.elim this
    disjoint_ranges := by
      intro i hi
      have : False := by simpa using hi
      exact False.elim this
  }
  attach := by
    intro i hi
    have : False := by simpa using hi
    exact False.elim this
  map_side := by
    intro i hi
    have : False := by simpa using hi
    exact False.elim this

/-- Merge two disjoint batches on one matching edge.  The second batch is
embedded into the exact residual endpoint sets left by the first. -/
noncomputable def appendPartial
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B)
    (externalParent : Fin b → B)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (whole available : Fin 2 → Finset B)
    (havailable : ∀ c, available c ⊆ whole c)
    (hwholeDisjoint : Disjoint (whole 0) (whole 1))
    (s t : Finset (Fin b)) (hst : Disjoint s t)
    (E₁ : PartialDynamicAttachedForestEmbedding
      F G externalParent orient available s)
    (E₂ : PartialDynamicAttachedForestEmbedding F G externalParent orient
      (fun c ↦ available c \ E₁.used c) t) :
    PartialDynamicAttachedForestEmbedding
      F G externalParent orient available (s ∪ t) := by
  classical
  let copy : ∀ i, i ∈ s ∪ t → (F.tree i).Copy G := fun i hi ↦
    if his : i ∈ s then E₁.forestCopy.componentCopy i his
    else E₂.forestCopy.componentCopy i ((Finset.mem_union.mp hi).resolve_left his)
  have hwholeDisjoint' : ∀ c d, c ≠ d → Disjoint (whole c) (whole d) := by
    intro c d hcd
    fin_cases c <;> fin_cases d
    · exact False.elim (hcd rfl)
    · exact hwholeDisjoint
    · exact hwholeDisjoint.symm
    · exact False.elim (hcd rfl)
  let FC : OrderedForestCopy (s ∪ t)
      (fun i ↦ Fin (F.size i)) (fun i ↦ F.tree i) G := {
    componentCopy := copy
    disjoint_ranges := by
      intro i hi j hj hij
      by_cases his : i ∈ s
      · by_cases hjs : j ∈ s
        · simpa only [copy, dif_pos his, dif_pos hjs] using
            E₁.forestCopy.disjoint_ranges i his j hjs hij
        · have hjt : j ∈ t := (Finset.mem_union.mp hj).resolve_left hjs
          rw [Set.disjoint_left]
          intro z hzi hzj
          obtain ⟨a, ha⟩ := hzi
          obtain ⟨d, hd⟩ := hzj
          have ha' : E₁.forestCopy.componentCopy i his a = z := by
            simpa only [copy, dif_pos his] using ha
          have hd' : E₂.forestCopy.componentCopy j hjt d = z := by
            simpa only [copy, dif_neg hjs] using hd
          let ci := orient i ((F.isTree i).coloringTwoOfVert (F.root i) a)
          let cj := orient j ((F.isTree j).coloringTwoOfVert (F.root j) d)
          have hai : E₁.forestCopy.componentCopy i his a ∈ available ci :=
            E₁.map_side i his a
          have hdj : E₂.forestCopy.componentCopy j hjt d ∈
              available cj \ E₁.used cj := E₂.map_side j hjt d
          by_cases hc : ci = cj
          · have hdjCi : E₂.forestCopy.componentCopy j hjt d ∈
                available ci \ E₁.used ci := by
              simpa only [hc] using hdj
            have haUsed := E₁.copy_mem_used i his a
            exact (Finset.mem_sdiff.mp hdjCi).2 (by
              rw [hd'.trans ha'.symm]
              exact haUsed)
          · have haWhole : E₁.forestCopy.componentCopy i his a ∈ whole ci :=
              havailable ci hai
            have hdWhole : E₂.forestCopy.componentCopy j hjt d ∈ whole cj :=
              havailable cj (Finset.mem_sdiff.mp hdj).1
            exact (Finset.disjoint_left.mp (hwholeDisjoint' ci cj hc) haWhole)
              ((ha'.trans hd'.symm).symm ▸ hdWhole)
      · have hit : i ∈ t := (Finset.mem_union.mp hi).resolve_left his
        by_cases hjs : j ∈ s
        · rw [Set.disjoint_left]
          intro z hzi hzj
          obtain ⟨a, ha⟩ := hzi
          obtain ⟨d, hd⟩ := hzj
          have ha' : E₂.forestCopy.componentCopy i hit a = z := by
            simpa only [copy, dif_neg his] using ha
          have hd' : E₁.forestCopy.componentCopy j hjs d = z := by
            simpa only [copy, dif_pos hjs] using hd
          let ci := orient i ((F.isTree i).coloringTwoOfVert (F.root i) a)
          let cj := orient j ((F.isTree j).coloringTwoOfVert (F.root j) d)
          have hai : E₂.forestCopy.componentCopy i hit a ∈
              available ci \ E₁.used ci := E₂.map_side i hit a
          have hdj : E₁.forestCopy.componentCopy j hjs d ∈ available cj :=
            E₁.map_side j hjs d
          by_cases hc : ci = cj
          · have hdUsedCi : E₁.forestCopy.componentCopy j hjs d ∈
                E₁.used ci := by
              simpa only [hc] using E₁.copy_mem_used j hjs d
            exact (Finset.mem_sdiff.mp hai).2 (by
              rw [ha'.trans hd'.symm]
              exact hdUsedCi)
          · have haWhole : E₂.forestCopy.componentCopy i hit a ∈ whole ci :=
              havailable ci (Finset.mem_sdiff.mp hai).1
            have hdWhole : E₁.forestCopy.componentCopy j hjs d ∈ whole cj :=
              havailable cj hdj
            exact (Finset.disjoint_left.mp (hwholeDisjoint' ci cj hc) haWhole)
              ((ha'.trans hd'.symm).symm ▸ hdWhole)
        · have hjt : j ∈ t := (Finset.mem_union.mp hj).resolve_left hjs
          simpa only [copy, dif_neg his, dif_neg hjs] using
            E₂.forestCopy.disjoint_ranges i hit j hjt hij
  }
  exact {
    forestCopy := FC
    attach := by
      intro i hi
      by_cases his : i ∈ s
      · simpa only [FC, copy, dif_pos his] using E₁.attach i his
      · have hit : i ∈ t := (Finset.mem_union.mp hi).resolve_left his
        simpa only [FC, copy, dif_neg his] using E₂.attach i hit
    map_side := by
      intro i hi a
      by_cases his : i ∈ s
      · simpa only [FC, copy, dif_pos his] using E₁.map_side i his a
      · have hit : i ∈ t := (Finset.mem_union.mp hi).resolve_left his
        exact (Finset.mem_sdiff.mp (by
          simpa only [FC, copy, dif_neg his] using E₂.map_side i hit a)).1
  }

/-! ### Sequential owner batching on one matching edge -/

/-- Selected components whose owner index is strictly before `n`. -/
def ownerPrefix {b r : ℕ} (selected : Finset (Fin b))
    (owner : Fin b → Fin r) (n : ℕ) : Finset (Fin b) :=
  selected.filter fun i ↦ (owner i).val < n

/-- The selected components belonging to one literal owner. -/
def ownerBatch {b r : ℕ} (selected : Finset (Fin b))
    (owner : Fin b → Fin r) (q : Fin r) : Finset (Fin b) :=
  selected.filter fun i ↦ owner i = q

@[simp] theorem ownerPrefix_zero {b r : ℕ}
    (selected : Finset (Fin b)) (owner : Fin b → Fin r) :
    ownerPrefix selected owner 0 = ∅ := by
  ext i
  simp [ownerPrefix]

theorem ownerPrefix_succ {b r : ℕ}
    (selected : Finset (Fin b)) (owner : Fin b → Fin r)
    (n : ℕ) (hn : n < r) :
    ownerPrefix selected owner n ∪ ownerBatch selected owner ⟨n, hn⟩ =
      ownerPrefix selected owner (n + 1) := by
  ext i
  simp only [ownerPrefix, ownerBatch, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨hi, hlt⟩ | ⟨hi, heq⟩)
    · exact ⟨hi, by omega⟩
    · have hval : (owner i).val = n := congrArg Fin.val heq
      exact ⟨hi, by omega⟩
  · rintro ⟨hi, hlt⟩
    by_cases hbefore : (owner i).val < n
    · exact Or.inl ⟨hi, hbefore⟩
    · apply Or.inr
      refine ⟨hi, Fin.ext ?_⟩
      simp only [Fin.val_mk]
      omega

theorem ownerPrefix_disjoint_ownerBatch {b r : ℕ}
    (selected : Finset (Fin b)) (owner : Fin b → Fin r)
    (n : ℕ) (hn : n < r) :
    Disjoint (ownerPrefix selected owner n)
      (ownerBatch selected owner ⟨n, hn⟩) := by
  apply Finset.disjoint_left.mpr
  intro i hip hib
  have hlt := (Finset.mem_filter.mp hip).2
  have heq := (Finset.mem_filter.mp hib).2
  have hval : (owner i).val = n := congrArg Fin.val heq
  omega

@[simp] theorem ownerPrefix_all {b r : ℕ}
    (selected : Finset (Fin b)) (owner : Fin b → Fin r) :
    ownerPrefix selected owner r = selected := by
  ext i
  simp only [ownerPrefix, Finset.mem_filter]
  constructor
  · exact And.left
  · intro hi
    exact ⟨hi, (owner i).isLt⟩

/-- Process the selected components on one matching edge owner by owner.

The local realization callback is invoked on the exact residual endpoint
sets left by the already constructed prefix.  In Part 3, the callback is
instantiated with the one-parent Appendix A.2/A.1 theorem after proving that
all components in `ownerBatch ... ⟨n,hn⟩` have the same external parent.
Thus no common root pool is ever shared across distinct owners. -/
theorem exists_partialDynamicEmbedding_of_ownerBatches
    {b r : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B)
    (externalParent : Fin b → B)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (whole available : Fin 2 → Finset B)
    (havailable : ∀ c, available c ⊆ whole c)
    (hwholeDisjoint : Disjoint (whole 0) (whole 1))
    (selected : Finset (Fin b)) (owner : Fin b → Fin r)
    (hstep : ∀ n (hn : n < r)
      (Eprefix : PartialDynamicAttachedForestEmbedding
        F G externalParent orient available (ownerPrefix selected owner n)),
      Nonempty (DynamicAttachedForestEmbedding
        (selectedForest F (ownerBatch selected owner ⟨n, hn⟩)) G
        (fun k ↦ externalParent
          (OrderedBranchForest.selectedEquiv
            (ownerBatch selected owner ⟨n, hn⟩) k))
        (fun k ↦ orient
          (OrderedBranchForest.selectedEquiv
            (ownerBatch selected owner ⟨n, hn⟩) k))
        (fun c ↦ available c \ Eprefix.used c))) :
    Nonempty (PartialDynamicAttachedForestEmbedding
      F G externalParent orient available selected) := by
  classical
  have hbuild : ∀ n, n ≤ r →
      Nonempty (PartialDynamicAttachedForestEmbedding
        F G externalParent orient available (ownerPrefix selected owner n)) := by
    intro n hnr
    induction n with
    | zero =>
        rw [ownerPrefix_zero]
        exact ⟨emptyPartial F G externalParent orient available⟩
    | succ n ih =>
        have hn : n < r := Nat.lt_of_succ_le hnr
        obtain ⟨Eprefix⟩ := ih (Nat.le_of_lt hn)
        obtain ⟨Ebatch⟩ := hstep n hn Eprefix
        let Pbatch : PartialDynamicAttachedForestEmbedding
            F G externalParent orient
              (fun c ↦ available c \ Eprefix.used c)
              (ownerBatch selected owner ⟨n, hn⟩) :=
          partialOfSelectedForest F G externalParent orient
            (fun c ↦ available c \ Eprefix.used c)
            (ownerBatch selected owner ⟨n, hn⟩) Ebatch
        have Eunion := appendPartial F G externalParent orient whole available
          havailable hwholeDisjoint (ownerPrefix selected owner n)
          (ownerBatch selected owner ⟨n, hn⟩)
          (ownerPrefix_disjoint_ownerBatch selected owner n hn)
          Eprefix Pbatch
        rw [ownerPrefix_succ selected owner n hn] at Eunion
        exact ⟨Eunion⟩
  obtain ⟨E⟩ := hbuild r le_rfl
  rw [ownerPrefix_all selected owner] at E
  exact ⟨E⟩

/-- Forget the partial-state indexing once every component has been
processed. -/
noncomputable def PartialDynamicAttachedForestEmbedding.toDynamic
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B)
    (externalParent : Fin b → B)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (available : Fin 2 → Finset B)
    (E : PartialDynamicAttachedForestEmbedding F G externalParent orient
      available Finset.univ) :
    DynamicAttachedForestEmbedding F G externalParent orient available := by
  let copy : ∀ i, (F.tree i).Copy G := fun i ↦
    E.forestCopy.componentCopy i (Finset.mem_univ i)
  have hinjective : Function.Injective
      (fun z : Σ i, Fin (F.size i) ↦ copy z.1 z.2) := by
    rintro ⟨i, a⟩ ⟨j, d⟩ hij
    by_cases hcomp : i = j
    · subst j
      have had : a = d := (copy i).injective hij
      subst d
      rfl
    · have hdisj := E.forestCopy.disjoint_ranges i (Finset.mem_univ i)
          j (Finset.mem_univ j) hcomp
      exfalso
      exact (Set.disjoint_left.mp hdisj) ⟨a, rfl⟩ ⟨d, hij.symm⟩
  exact {
    embedding := ⟨copy, hinjective⟩
    attach := by
      intro i
      exact E.attach i (Finset.mem_univ i)
    map_side := by
      intro i a
      exact E.map_side i (Finset.mem_univ i) a
  }

/-- Full-family version of owner batching, ready to serve as the one-edge
local witness consumed by `Lemma58MatchingAssembly`. -/
theorem exists_dynamicAttachedForestEmbedding_of_ownerBatches
    {b r : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B)
    (externalParent : Fin b → B)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (whole available : Fin 2 → Finset B)
    (havailable : ∀ c, available c ⊆ whole c)
    (hwholeDisjoint : Disjoint (whole 0) (whole 1))
    (owner : Fin b → Fin r)
    (hstep : ∀ n (hn : n < r)
      (Eprefix : PartialDynamicAttachedForestEmbedding F G externalParent
        orient available (ownerPrefix Finset.univ owner n)),
      Nonempty (DynamicAttachedForestEmbedding
        (selectedForest F (ownerBatch Finset.univ owner ⟨n, hn⟩)) G
        (fun k ↦ externalParent
          (OrderedBranchForest.selectedEquiv
            (ownerBatch Finset.univ owner ⟨n, hn⟩) k))
        (fun k ↦ orient
          (OrderedBranchForest.selectedEquiv
            (ownerBatch Finset.univ owner ⟨n, hn⟩) k))
        (fun c ↦ available c \ Eprefix.used c))) :
    Nonempty (DynamicAttachedForestEmbedding
      F G externalParent orient available) := by
  obtain ⟨E⟩ := exists_partialDynamicEmbedding_of_ownerBatches
    F G externalParent orient whole available havailable hwholeDisjoint
    Finset.univ owner hstep
  exact ⟨E.toDynamic F G externalParent orient available⟩

end Erdos547b.ZhaoLemma58DynamicBatchAppend

#print axioms Erdos547b.ZhaoLemma58DynamicBatchAppend.appendPartial
#print axioms Erdos547b.ZhaoLemma58DynamicBatchAppend.PartialDynamicAttachedForestEmbedding.toDynamic
