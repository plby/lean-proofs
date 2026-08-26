/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58GroupedSmallForest
import ErdosProblems.Erdos547b.Claim616SourceBridge

/-!
# Assembly of the matching-edge realizations in Zhao Lemma 5.8

The dynamic regular-pair argument realizes, for each matching edge, the
subfamily of branches assigned to that edge.  This file performs the purely
graph-theoretic last step: it reindexes those fiber embeddings by the
original branch indices and glues them.  Images belonging to different
matching edges are disjoint because the two endpoint supports of distinct
matching edges are disjoint.

There is no embedding or copy conclusion among the assumptions.  The local
objects are the concrete output of `exists_dynamic_ordered_forest_embedding_of_uniform`.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoLemma58MatchingAssembly

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest

universe v

/-- The original branches assigned to one matching edge. -/
def matchingFiber {b k : ℕ} (assign : Fin b → Fin k) (e : Fin k) :
    Finset (Fin b) :=
  Finset.univ.filter fun j ↦ assign j = e

@[simp] theorem mem_matchingFiber {b k : ℕ}
    (assign : Fin b → Fin k) (e : Fin k) (j : Fin b) :
    j ∈ matchingFiber assign e ↔ assign j = e := by
  simp [matchingFiber]

/-- The coordinate of an original branch in the canonical enumeration of
its assignment fiber. -/
noncomputable def assignmentIndex {b k : ℕ}
    (assign : Fin b → Fin k) (j : Fin b) :
    Fin (matchingFiber assign (assign j)).card :=
  (OrderedBranchForest.selectedEquiv
    (matchingFiber assign (assign j))).symm
      ⟨j, by simp⟩

@[simp] theorem selectedEquiv_assignmentIndex {b k : ℕ}
    (assign : Fin b → Fin k) (j : Fin b) :
    (((OrderedBranchForest.selectedEquiv
      (matchingFiber assign (assign j))) (assignmentIndex assign j) :
        {x // x ∈ matchingFiber assign (assign j)}) : Fin b) = j := by
  simp [assignmentIndex]

/-- The vertex coordinate in the restricted forest corresponding to an
original branch coordinate. -/
noncomputable def assignmentVertex {r b k : ℕ}
    (F : OrderedBranchForest r b) (assign : Fin b → Fin k)
    (j : Fin b) (a : Fin (F.branches.size j)) :
    Fin ((Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.restrict F
      (matchingFiber assign (assign j))).branches.size
      (assignmentIndex assign j)) :=
  Fin.cast (by
    simp only [
      Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.restrict_size,
      selectedEquiv_assignmentIndex]) a

@[simp] theorem assignmentVertex_val {r b k : ℕ}
    (F : OrderedBranchForest r b) (assign : Fin b → Fin k)
    (j : Fin b) (a : Fin (F.branches.size j)) :
    (assignmentVertex F assign j a).val = a.val := by
  rfl

theorem assignmentVertex_injective {r b k : ℕ}
    (F : OrderedBranchForest r b) (assign : Fin b → Fin k)
    (j : Fin b) : Function.Injective (assignmentVertex F assign j) := by
  intro a a' haa'
  apply Fin.ext
  simpa using congrArg Fin.val haa'

private theorem branch_tree_adj_cast_index {r b : ℕ}
    (F : OrderedBranchForest r b) {i j : Fin b} (hji : j = i)
    (a d : Fin (F.branches.size i))
    (had : (F.branches.tree i).Adj a d) :
    (F.branches.tree j).Adj
      (Fin.cast (congrArg F.branches.size hji.symm) a)
      (Fin.cast (congrArg F.branches.size hji.symm) d) := by
  subst j
  simpa using had

private theorem branch_coloring_cast_index {r b : ℕ}
    (F : OrderedBranchForest r b) {i j : Fin b} (hji : j = i)
    (a : Fin (F.branches.size i)) :
    (F.branches.isTree j).coloringTwoOfVert (F.branches.root j)
        (Fin.cast (congrArg F.branches.size hji.symm) a) =
      (F.branches.isTree i).coloringTwoOfVert (F.branches.root i) a := by
  subst j
  rfl

@[simp] theorem assignmentVertex_root {r b k : ℕ}
    (F : OrderedBranchForest r b) (assign : Fin b → Fin k) (j : Fin b) :
    assignmentVertex F assign j (F.branches.root j) =
      (Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.restrict F
        (matchingFiber assign (assign j))).branches.root
          (assignmentIndex assign j) := by
  have hidx := selectedEquiv_assignmentIndex assign j
  apply Fin.ext
  change (F.branches.root j).val =
    (F.branches.root (OrderedBranchForest.selectedEquiv
      (matchingFiber assign (assign j)) (assignmentIndex assign j))).val
  exact (congrArg (fun t ↦ (F.branches.root t).val) hidx).symm

/-- The canonical assignment-fiber coordinate preserves the rooted
two-colouring of its literal original branch. -/
@[simp] theorem assignmentVertex_coloring {r b k : ℕ}
    (F : OrderedBranchForest r b) (assign : Fin b → Fin k)
    (j : Fin b) (a : Fin (F.branches.size j)) :
    ((Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.restrict F
        (matchingFiber assign (assign j))).branches.isTree
          (assignmentIndex assign j)).coloringTwoOfVert
      ((Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.restrict F
        (matchingFiber assign (assign j))).branches.root
          (assignmentIndex assign j))
      (assignmentVertex F assign j a) =
    (F.branches.isTree j).coloringTwoOfVert (F.branches.root j) a := by
  have hidx := selectedEquiv_assignmentIndex assign j
  have hvertex : assignmentVertex F assign j a =
      Fin.cast (congrArg F.branches.size hidx.symm) a := by
    apply Fin.ext
    rfl
  rw [hvertex]
  exact branch_coloring_cast_index F hidx a

/-- Coordinate of a branch in an explicitly named assignment fiber. -/
noncomputable def fiberIndex {b k : ℕ} (assign : Fin b → Fin k)
    (e : Fin k) (j : Fin b) (hj : assign j = e) :
    Fin (matchingFiber assign e).card :=
  (OrderedBranchForest.selectedEquiv (matchingFiber assign e)).symm
    ⟨j, by simp [hj]⟩

/-- Vertex coordinate in an explicitly named assignment fiber. -/
noncomputable def fiberVertex {r b k : ℕ}
    (F : OrderedBranchForest r b) (assign : Fin b → Fin k)
    (e : Fin k) (j : Fin b) (hj : assign j = e)
    (a : Fin (F.branches.size j)) :
    Fin ((Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.restrict F
      (matchingFiber assign e)).branches.size
      (fiberIndex assign e j hj)) :=
  Fin.cast (by
    simp only [
      Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.restrict_size,
      fiberIndex, Equiv.apply_symm_apply]) a

/-- The local data expected on each matching edge.  Naming this family keeps
the public assembly statement readable and fixes the exact reindexing used
by the dynamic Lemma-5.8 realization. -/
abbrev FiberEmbeddingFamily {r b k : ℕ} {B : Type v}
    [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B)
    (rootImage : Fin r → B) (assign : Fin b → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (orient : Fin b → Fin 2 ≃ Fin 2) :=
  ∀ e, DynamicAttachedForestEmbedding
    (Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.restrict F
      (matchingFiber assign e)).branches G
    (fun i ↦ rootImage (F.owner
      (OrderedBranchForest.selectedEquiv (matchingFiber assign e) i)))
    (fun i ↦ orient
      (OrderedBranchForest.selectedEquiv (matchingFiber assign e) i))
    (endpoint e)

/-- Pull one locally embedded component back to its original branch index. -/
noncomputable def assembledBranchCopy {r b k : ℕ} {B : Type v}
    [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B)
    (rootImage : Fin r → B) (assign : Fin b → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (localEmb : FiberEmbeddingFamily F G rootImage assign endpoint orient)
    (j : Fin b) : (F.branches.tree j).Copy G where
  toHom :=
    { toFun := fun a ↦
        (localEmb (assign j)).embedding.copy (assignmentIndex assign j)
          (assignmentVertex F assign j a)
      map_rel' := by
        intro a a' haa'
        apply (localEmb (assign j)).embedding.copy
          (assignmentIndex assign j) |>.toHom.map_rel
        have hidx := selectedEquiv_assignmentIndex assign j
        simpa only [
          Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.restrict,
          assignmentVertex] using
            branch_tree_adj_cast_index F hidx a a' haa' }
  injective' :=
    ((localEmb (assign j)).embedding.copy
      (assignmentIndex assign j)).injective.comp
        (assignmentVertex_injective F assign j)

@[simp] theorem assembledBranchCopy_apply {r b k : ℕ} {B : Type v}
    [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B)
    (rootImage : Fin r → B) (assign : Fin b → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (localEmb : FiberEmbeddingFamily F G rootImage assign endpoint orient)
    (j : Fin b) (a : Fin (F.branches.size j)) :
    assembledBranchCopy F G rootImage assign endpoint orient localEmb j a =
      (localEmb (assign j)).embedding.copy (assignmentIndex assign j)
        (assignmentVertex F assign j a) := rfl

/-- The assembled application expressed in one explicitly named fiber. -/
theorem assembledBranchCopy_apply_on_fiber
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B)
    (rootImage : Fin r → B) (assign : Fin b → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (localEmb : FiberEmbeddingFamily F G rootImage assign endpoint orient)
    (e : Fin k) (j : Fin b) (hj : assign j = e)
    (a : Fin (F.branches.size j)) :
    assembledBranchCopy F G rootImage assign endpoint orient localEmb j a =
      (localEmb e).embedding.copy (fiberIndex assign e j hj)
        (fiberVertex F assign e j hj a) := by
  subst e
  rfl

theorem assembledBranchCopy_mem {r b k : ℕ} {B : Type v}
    [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B)
    (rootImage : Fin r → B) (assign : Fin b → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (localEmb : FiberEmbeddingFamily F G rootImage assign endpoint orient)
    (j : Fin b) (a : Fin (F.branches.size j)) :
    assembledBranchCopy F G rootImage assign endpoint orient localEmb j a ∈
      endpoint (assign j) (orient j
        ((F.branches.isTree j).coloringTwoOfVert
          (F.branches.root j) a)) := by
  rw [assembledBranchCopy_apply]
  have hidx := selectedEquiv_assignmentIndex assign j
  have hm := (localEmb (assign j)).map_side (assignmentIndex assign j)
    (assignmentVertex F assign j a)
  change (localEmb (assign j)).embedding.copy (assignmentIndex assign j)
      (assignmentVertex F assign j a) ∈
    endpoint (assign j) (orient
      (OrderedBranchForest.selectedEquiv
        (matchingFiber assign (assign j)) (assignmentIndex assign j))
      ((F.branches.isTree (OrderedBranchForest.selectedEquiv
        (matchingFiber assign (assign j))
        (assignmentIndex assign j))).coloringTwoOfVert
        (F.branches.root (OrderedBranchForest.selectedEquiv
          (matchingFiber assign (assign j))
          (assignmentIndex assign j)))
        (assignmentVertex F assign j a))) at hm
  have hvertex : assignmentVertex F assign j a =
      Fin.cast (congrArg F.branches.size hidx.symm) a := by
    apply Fin.ext
    rfl
  have horient := congrArg orient hidx
  have hcolor :
      (F.branches.isTree (OrderedBranchForest.selectedEquiv
        (matchingFiber assign (assign j))
        (assignmentIndex assign j))).coloringTwoOfVert
          (F.branches.root (OrderedBranchForest.selectedEquiv
            (matchingFiber assign (assign j))
            (assignmentIndex assign j)))
          (assignmentVertex F assign j a) =
        (F.branches.isTree j).coloringTwoOfVert
          (F.branches.root j) a := by
    rw [hvertex]
    exact branch_coloring_cast_index F hidx a
  rw [horient, hcolor] at hm
  exact hm

theorem assembledBranchCopy_attach {r b k : ℕ} {B : Type v}
    [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B)
    (rootImage : Fin r → B) (assign : Fin b → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (localEmb : FiberEmbeddingFamily F G rootImage assign endpoint orient)
    (j : Fin b) :
    G.Adj (rootImage (F.owner j))
      (assembledBranchCopy F G rootImage assign endpoint orient localEmb j
        (F.branches.root j)) := by
  rw [assembledBranchCopy_apply]
  have hidx := selectedEquiv_assignmentIndex assign j
  have ha := (localEmb (assign j)).attach (assignmentIndex assign j)
  change G.Adj (rootImage (F.owner
      (OrderedBranchForest.selectedEquiv
        (matchingFiber assign (assign j)) (assignmentIndex assign j))))
    ((localEmb (assign j)).embedding.copy (assignmentIndex assign j)
      ((Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.restrict F
          (matchingFiber assign (assign j))).branches.root
          (assignmentIndex assign j))) at ha
  have hparent := congrArg (fun t ↦ rootImage (F.owner t)) hidx
  rw [hparent] at ha
  simpa only [assignmentVertex_root] using ha

/-- Assemble the concrete dynamic embeddings on all matching-edge fibers.
The only interaction between distinct fibers is disjointness of their two
endpoint supports. -/
noncomputable def rootAttachedBranchEmbeddingOfMatchingFibers
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B)
    (rootImage : Fin r → B) (assign : Fin b → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (localEmb : FiberEmbeddingFamily F G rootImage assign endpoint orient)
    (hsupportDisjoint : ∀ e e', e ≠ e' →
      Disjoint (endpoint e 0 ∪ endpoint e 1)
        (endpoint e' 0 ∪ endpoint e' 1)) :
    RootAttachedBranchEmbedding F G rootImage
      (fun j c ↦ endpoint (assign j) c) orient where
  branchEmbedding :=
    { copy := assembledBranchCopy F G rootImage assign endpoint orient localEmb
      injective := by
        rintro ⟨j, a⟩ ⟨j', a'⟩ hEq
        change assembledBranchCopy F G rootImage assign endpoint orient localEmb j a =
          assembledBranchCopy F G rootImage assign endpoint orient localEmb j' a' at hEq
        by_cases hjj' : j = j'
        · subst j'
          have haa' :=
            (assembledBranchCopy F G rootImage assign endpoint orient localEmb j).injective hEq
          refine Sigma.ext (by rfl) ?_
          exact heq_of_eq haa'
        · have hassign : assign j ≠ assign j' := by
            intro he
            let e := assign j
            let s := matchingFiber assign e
            have hej : assign j = e := rfl
            have hej' : assign j' = e := by
              exact he.symm.trans hej
            let i : Fin s.card := fiberIndex assign e j hej
            let i' : Fin s.card := fiberIndex assign e j' hej'
            let aLocal :
                Fin ((Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.restrict F s).branches.size i) := by
              exact fiberVertex F assign e j hej a
            let aLocal' :
                Fin ((Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.restrict F s).branches.size i') := by
              exact fiberVertex F assign e j' hej' a'
            have hlocalEq :
                (localEmb e).embedding.copy i aLocal =
                  (localEmb e).embedding.copy i' aLocal' := by
              calc
                (localEmb e).embedding.copy i aLocal =
                    assembledBranchCopy F G rootImage assign endpoint orient
                      localEmb j a := by
                  symm
                  exact assembledBranchCopy_apply_on_fiber F G rootImage
                    assign endpoint orient localEmb e j hej a
                _ = assembledBranchCopy F G rootImage assign endpoint orient
                      localEmb j' a' := hEq
                _ = (localEmb e).embedding.copy i' aLocal' := by
                  exact assembledBranchCopy_apply_on_fiber F G rootImage
                    assign endpoint orient localEmb e j' hej' a'
            have hsigma :
                (⟨i, aLocal⟩ : Σ z, Fin
                  ((Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.restrict F s).branches.size z)) =
                  ⟨i', aLocal'⟩ :=
              (localEmb e).embedding.injective hlocalEq
            have hii' : i = i' := congrArg Sigma.fst hsigma
            have hbranch := congrArg (fun z ↦
              ((OrderedBranchForest.selectedEquiv s z : {x // x ∈ s}) : Fin b)) hii'
            apply hjj'
            have hjSpec :
                ((OrderedBranchForest.selectedEquiv s i : {x // x ∈ s}) :
                  Fin b) = j := by
              simp only [s, i, fiberIndex, Equiv.apply_symm_apply]
            have hj'Spec :
                ((OrderedBranchForest.selectedEquiv s i' : {x // x ∈ s}) :
                  Fin b) = j' := by
              simp only [s, i', fiberIndex, Equiv.apply_symm_apply]
            exact hjSpec.symm.trans (hbranch.trans hj'Spec)
          have haMem := assembledBranchCopy_mem F G rootImage assign
            endpoint orient localEmb j a
          have ha'Mem := assembledBranchCopy_mem F G rootImage assign
            endpoint orient localEmb j' a'
          have haUnion :
              assembledBranchCopy F G rootImage assign endpoint orient localEmb j a ∈
                endpoint (assign j) 0 ∪ endpoint (assign j) 1 := by
            rcases OrderedRootedForest.fin_two_eq_zero_or_one
                (orient j ((F.branches.isTree j).coloringTwoOfVert
                  (F.branches.root j) a)) with hc | hc
            · rw [hc] at haMem
              exact Finset.mem_union_left _ haMem
            · rw [hc] at haMem
              exact Finset.mem_union_right _ haMem
          have ha'Union :
              assembledBranchCopy F G rootImage assign endpoint orient localEmb j' a' ∈
                endpoint (assign j') 0 ∪ endpoint (assign j') 1 := by
            rcases OrderedRootedForest.fin_two_eq_zero_or_one
                (orient j' ((F.branches.isTree j').coloringTwoOfVert
                  (F.branches.root j') a')) with hc | hc
            · rw [hc] at ha'Mem
              exact Finset.mem_union_left _ ha'Mem
            · rw [hc] at ha'Mem
              exact Finset.mem_union_right _ ha'Mem
          have hImageEq :
              assembledBranchCopy F G rootImage assign endpoint orient localEmb j a =
                assembledBranchCopy F G rootImage assign endpoint orient localEmb j' a' := hEq
          rw [← hImageEq] at ha'Union
          exact False.elim
            ((Finset.disjoint_left.mp
              (hsupportDisjoint (assign j) (assign j') hassign))
                haUnion ha'Union) }
  attach := assembledBranchCopy_attach F G rootImage assign endpoint orient localEmb
  map_branch := assembledBranchCopy_mem F G rootImage assign endpoint orient localEmb

/-- Existential wrapper matching the output form of the per-edge dynamic
embedding theorem. -/
theorem exists_rootAttachedBranchEmbedding_of_matchingFibers
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B)
    (rootImage : Fin r → B) (assign : Fin b → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (hlocal : ∀ e, Nonempty (DynamicAttachedForestEmbedding
      (Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.restrict F
        (matchingFiber assign e)).branches G
      (fun i ↦ rootImage (F.owner
        (OrderedBranchForest.selectedEquiv (matchingFiber assign e) i)))
      (fun i ↦ orient
        (OrderedBranchForest.selectedEquiv (matchingFiber assign e) i))
      (endpoint e)))
    (hsupportDisjoint : ∀ e e', e ≠ e' →
      Disjoint (endpoint e 0 ∪ endpoint e 1)
        (endpoint e' 0 ∪ endpoint e' 1)) :
    Nonempty (RootAttachedBranchEmbedding F G rootImage
      (fun j c ↦ endpoint (assign j) c) orient) := by
  classical
  let localEmb : FiberEmbeddingFamily F G rootImage assign endpoint orient :=
    fun e ↦ Classical.choice (hlocal e)
  exact ⟨rootAttachedBranchEmbeddingOfMatchingFibers F G rootImage assign
    endpoint orient localEmb hsupportDisjoint⟩

/-- The corresponding literal copy of the whole branch forest.  Root/root
collisions are excluded by `hrootInjective`; root/branch collisions are
excluded by membership in, and avoidance of, the matching endpoint pools. -/
theorem exists_graphCopy_of_matchingFibers
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B)
    (rootImage : Fin r → B) (assign : Fin b → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (hlocal : ∀ e, Nonempty (DynamicAttachedForestEmbedding
      (Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.restrict F
        (matchingFiber assign e)).branches G
      (fun i ↦ rootImage (F.owner
        (OrderedBranchForest.selectedEquiv (matchingFiber assign e) i)))
      (fun i ↦ orient
        (OrderedBranchForest.selectedEquiv (matchingFiber assign e) i))
      (endpoint e)))
    (hsupportDisjoint : ∀ e e', e ≠ e' →
      Disjoint (endpoint e 0 ∪ endpoint e 1)
        (endpoint e' 0 ∪ endpoint e' 1))
    (hrootInjective : Function.Injective rootImage)
    (hrootOutside : ∀ q e c, rootImage q ∉ endpoint e c) :
    Nonempty (F.graph.Copy G) := by
  obtain ⟨E⟩ := exists_rootAttachedBranchEmbedding_of_matchingFibers
    F G rootImage assign endpoint orient hlocal hsupportDisjoint
  apply Nonempty.intro
  apply E.toGraphCopy F G rootImage (fun j c ↦ endpoint (assign j) c)
    orient hrootInjective
  intro q i a hEq
  have hmem := E.map_branch i a
  exact hrootOutside q (assign i)
    (orient i ((F.branches.isTree i).coloringTwoOfVert
      (F.branches.root i) a)) (hEq.symm ▸ hmem)

#print axioms exists_rootAttachedBranchEmbedding_of_matchingFibers
#print axioms exists_graphCopy_of_matchingFibers

end Erdos547b.ZhaoLemma58MatchingAssembly
