/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.HierarchicalSpecialEmbedding
import ErdosProblems.Erdos547b.HierarchicalCanonicalCleaning
import ErdosProblems.Erdos547b.Claim68BranchGraphTransport
import ErdosProblems.Erdos547b.SingleTreeOrderedForest

/-!
# Zhao Lemma 6.14: full-tree hierarchical backend

Instead of embedding the Zhao cut forest and assuming that the deleted
root--parent edges can be restored, regard the literal input tree as a
one-component ordered forest.  Its root-deleted branches are segmented at
all vertices where the host layer changes (in the application: every later
Zhao component root and the optional parent set from Lemma 6.3).  The online
hierarchy then contains every former cut edge as an actual parent edge.

The public theorem below has no `Copy`, containment, continuation, or
parent-adjacency hypothesis.  It consumes the concrete cleaned regular
system and returns a literal copy of `T`.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoLemma614HierarchicalFullTree

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoLemma59SpecialSegmentation
open Erdos547b.ZhaoLemma59HierarchicalSpecial
open Erdos547b.ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest
open Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim68BranchGraphTransport
open Erdos547b.ZhaoSingleTreeOrderedForest
open Erdos547b.TreePartition

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {B : Type v} [Fintype B] [DecidableEq B]

abbrev wholeOrderedTree (T : SimpleGraph V) (hT : T.IsTree) (root : V) :=
  singleOrderedRootedTree T hT root

abbrev wholeBranchForest (T : SimpleGraph V) (hT : T.IsTree) (root : V) :=
  toOrderedBranchForest (wholeOrderedTree T hT root)

abbrev WholeBranchVertex (T : SimpleGraph V) (hT : T.IsTree) (root : V) :=
  BranchVertex (wholeBranchForest T hT root)

/-- Literal source vertex represented by a coordinate of the reconstructed
one-root branch forest, before special segmentation. -/
def wholeBranchOriginalVertex
    (T : SimpleGraph V) (hT : T.IsTree) (root : V) :
    (wholeBranchForest T hT root).Vertex → V :=
  fun x ↦ fromSingleCoordinate T hT root
    (flattenBranch (wholeOrderedTree T hT root) x)

/-- Coordinate of a literal tree vertex in the reconstructed one-root
branch forest. -/
def toWholeBranchForestVertex
    (T : SimpleGraph V) (hT : T.IsTree) (root : V) :
    V → (wholeBranchForest T hT root).Vertex :=
  fun x ↦ (branchGraphIso (wholeOrderedTree T hT root)).symm
    (toSingleCoordinate T hT root x)

theorem toWholeBranchForestVertex_injective
    (T : SimpleGraph V) (hT : T.IsTree) (root : V) :
    Function.Injective (toWholeBranchForestVertex T hT root) := by
  intro x y hxy
  apply toSingleCoordinate_injective T hT root
  exact (branchGraphIso (wholeOrderedTree T hT root)).symm.injective hxy

@[simp] theorem toWholeBranchForestVertex_root
    (T : SimpleGraph V) (hT : T.IsTree) (root : V) :
    toWholeBranchForestVertex T hT root root = Sum.inl 0 := by
  let e := branchGraphIso (wholeOrderedTree T hT root)
  apply e.injective
  change e (e.symm (toSingleCoordinate T hT root root)) =
    e (Sum.inl 0)
  rw [e.apply_symm_apply]
  change toSingleCoordinate T hT root root =
    flattenBranch (wholeOrderedTree T hT root) (Sum.inl 0)
  rw [toSingleCoordinate_root, flattenBranch_root]

theorem wholeBranchOriginal_branch
    (T : SimpleGraph V) (hT : T.IsTree) (root : V)
    (j : Fin (Fintype.card (ChildKey (wholeOrderedTree T hT root))))
    (a : Fin ((wholeBranchForest T hT root).branches.size j)) :
    wholeBranchOriginalVertex T hT root (Sum.inr ⟨j, a⟩) =
      vertexEquiv (branchLocalVertex (wholeOrderedTree T hT root) j a) := by
  rw [wholeBranchOriginalVertex, flattenBranch_branch_eq_local]
  rfl

theorem wholeBranchOriginal_branch_ne_root
    (T : SimpleGraph V) (hT : T.IsTree) (root : V)
    (j : Fin (Fintype.card (ChildKey (wholeOrderedTree T hT root))))
    (a : Fin ((wholeBranchForest T hT root).branches.size j)) :
    wholeBranchOriginalVertex T hT root (Sum.inr ⟨j, a⟩) ≠ root := by
  rw [wholeBranchOriginal_branch]
  intro heq
  apply branchLocalVertex_ne_componentRoot
    (wholeOrderedTree T hT root) j a
  apply (vertexEquiv (V := V)).injective
  simpa [wholeOrderedTree, singleOrderedRootedTree] using heq

/-- Parent transport through the canonical one-component reindexing. -/
theorem singleOrdered_parent_original
    (T : SimpleGraph V) (hT : T.IsTree) (root : V)
    (a : Fin (Fintype.card V))
    (ha : a ≠ (wholeOrderedTree T hT root).root 0) :
    vertexEquiv
        (TreePartition.parent ((wholeOrderedTree T hT root).isTree 0)
          ((wholeOrderedTree T hT root).root 0) ha) =
      TreePartition.parent hT root
        (by
          intro h
          apply ha
          apply (vertexEquiv (V := V)).injective
          simpa [wholeOrderedTree, singleOrderedRootedTree] using h) := by
  let p := TreePartition.parent ((wholeOrderedTree T hT root).isTree 0)
    ((wholeOrderedTree T hT root).root 0) ha
  have hAdjLocal := TreePartition.parent_adj
    ((wholeOrderedTree T hT root).isTree 0)
    ((wholeOrderedTree T hT root).root 0) ha
  have hAdj : T.Adj (vertexEquiv p) (vertexEquiv a) := by
    exact hAdjLocal
  have hDistLocal := TreePartition.parent_dist_add_one
    ((wholeOrderedTree T hT root).isTree 0)
    ((wholeOrderedTree T hT root).root 0) ha
  let e : (wholeOrderedTree T hT root).tree 0 ≃g T :=
    SimpleGraph.Iso.comap (vertexEquiv (V := V)) T
  have hpIso := graphIso_dist_eq_of_reachable e
    (((wholeOrderedTree T hT root).isTree 0).connected
      ((wholeOrderedTree T hT root).root 0) p)
  have haIso := graphIso_dist_eq_of_reachable e
    (((wholeOrderedTree T hT root).isTree 0).connected
      ((wholeOrderedTree T hT root).root 0) a)
  have hrootImage : vertexEquiv
      ((wholeOrderedTree T hT root).root 0) = root := by
    change vertexEquiv ((vertexEquiv (V := V)).symm root) = root
    exact (vertexEquiv (V := V)).apply_symm_apply root
  change T.dist (vertexEquiv ((wholeOrderedTree T hT root).root 0))
      (vertexEquiv p) =
        ((wholeOrderedTree T hT root).tree 0).dist
          ((wholeOrderedTree T hT root).root 0) p at hpIso
  change T.dist (vertexEquiv ((wholeOrderedTree T hT root).root 0))
      (vertexEquiv a) =
        ((wholeOrderedTree T hT root).tree 0).dist
          ((wholeOrderedTree T hT root).root 0) a at haIso
  rw [hrootImage] at hpIso haIso
  have hDist : T.dist root (vertexEquiv p) + 1 =
      T.dist root (vertexEquiv a) := by
    calc
      T.dist root (vertexEquiv p) + 1 =
          ((wholeOrderedTree T hT root).tree 0).dist
            ((wholeOrderedTree T hT root).root 0) p + 1 := by
        exact congrArg (fun n ↦ n + 1) hpIso
      _ = ((wholeOrderedTree T hT root).tree 0).dist
            ((wholeOrderedTree T hT root).root 0) a := hDistLocal
      _ = T.dist root (vertexEquiv a) := by
        exact haIso.symm
  exact TreePartition.eq_parent_of_adj_of_dist_add_one hT root _ hAdj hDist

/-- Literal whole-tree spelling of `flattenBranch_localParent`.  This is the
boundary theorem consumed by the F₀/F₁/F_b hierarchy classifier. -/
theorem wholeBranch_localParent_original
    (T : SimpleGraph V) (hT : T.IsTree) (globalRoot : V)
    (j : Fin (Fintype.card (ChildKey
      (wholeOrderedTree T hT globalRoot))))
    (a : Fin ((wholeBranchForest T hT globalRoot).branches.size j))
    (ha : a ≠ (wholeBranchForest T hT globalRoot).branches.root j) :
    let p := TreePartition.parent
      ((wholeBranchForest T hT globalRoot).branches.isTree j)
      ((wholeBranchForest T hT globalRoot).branches.root j) ha
    wholeBranchOriginalVertex T hT globalRoot (Sum.inr ⟨j, p⟩) =
      TreePartition.parent hT globalRoot
        (wholeBranchOriginal_branch_ne_root T hT globalRoot j a) := by
  dsimp only
  let p := TreePartition.parent
    ((wholeBranchForest T hT globalRoot).branches.isTree j)
    ((wholeBranchForest T hT globalRoot).branches.root j) ha
  have hflat := flattenBranch_localParent
    (wholeOrderedTree T hT globalRoot) j a ha
  have howner : (childKeyEquiv
      (wholeOrderedTree T hT globalRoot) j).1.1 = 0 := Subsingleton.elim _ _
  change fromSingleCoordinate T hT globalRoot
      (flattenBranch (wholeOrderedTree T hT globalRoot) (Sum.inr ⟨j, p⟩)) = _
  rw [hflat]
  change vertexEquiv
      (TreePartition.parent
        ((wholeOrderedTree T hT globalRoot).isTree
          (childKeyEquiv (wholeOrderedTree T hT globalRoot) j).1.1)
        ((wholeOrderedTree T hT globalRoot).root
          (childKeyEquiv (wholeOrderedTree T hT globalRoot) j).1.1)
        (branchLocalVertex_ne_componentRoot
          (wholeOrderedTree T hT globalRoot) j a)) = _
  rw [howner]
  let a₀ := branchLocalVertex (wholeOrderedTree T hT globalRoot) j a
  have ha₀ : a₀ ≠ (wholeOrderedTree T hT globalRoot).root 0 := by
    intro h
    apply branchLocalVertex_ne_componentRoot
      (wholeOrderedTree T hT globalRoot) j a
    rw [howner]
    exact h
  have hvertex :
      wholeBranchOriginalVertex T hT globalRoot (Sum.inr ⟨j, a⟩) =
        vertexEquiv a₀ := by
    simpa [a₀] using wholeBranchOriginal_branch T hT globalRoot j a
  have hxWhole := wholeBranchOriginal_branch_ne_root T hT globalRoot j a
  have ha₀Original : vertexEquiv a₀ ≠ globalRoot := by
    intro h
    apply hxWhole
    rw [hvertex, h]
  have hsingleRaw := singleOrdered_parent_original T hT globalRoot a₀ ha₀
  have hsingle :
      vertexEquiv
          (TreePartition.parent ((wholeOrderedTree T hT globalRoot).isTree 0)
            ((wholeOrderedTree T hT globalRoot).root 0) ha₀) =
        TreePartition.parent hT globalRoot ha₀Original := by
    refine hsingleRaw.trans ?_
    exact congrArg
      (fun hx : vertexEquiv a₀ ≠ globalRoot ↦
        TreePartition.parent hT globalRoot hx)
      (proof_irrel _ _)
  have hadj : T.Adj
      (vertexEquiv
        (TreePartition.parent ((wholeOrderedTree T hT globalRoot).isTree 0)
          ((wholeOrderedTree T hT globalRoot).root 0) ha₀))
      (wholeBranchOriginalVertex T hT globalRoot (Sum.inr ⟨j, a⟩)) := by
    rw [hsingle, hvertex]
    exact TreePartition.parent_adj hT globalRoot ha₀Original
  have hdist : T.dist globalRoot
        (vertexEquiv
          (TreePartition.parent ((wholeOrderedTree T hT globalRoot).isTree 0)
            ((wholeOrderedTree T hT globalRoot).root 0) ha₀)) + 1 =
      T.dist globalRoot
        (wholeBranchOriginalVertex T hT globalRoot (Sum.inr ⟨j, a⟩)) := by
    rw [hsingle, hvertex]
    exact TreePartition.parent_dist_add_one hT globalRoot ha₀Original
  exact TreePartition.eq_parent_of_adj_of_dist_add_one hT globalRoot
    (wholeBranchOriginal_branch_ne_root T hT globalRoot j a) hadj hdist

/-- Turn literal vertices to be exposed as new hierarchy roots into branch
coordinates.  The unique original root, if present, is deliberately ignored;
all genuine branch roots are added by `marks` automatically. -/
def wholeSpecialCoordinates
    (T : SimpleGraph V) (hT : T.IsTree) (root : V)
    (markedVertices : Finset V) :
    Finset (WholeBranchVertex T hT root) :=
  branchSpecial (wholeBranchForest T hT root)
    (markedVertices.image (toWholeBranchForestVertex T hT root))

/-- Literal Level-1 roots of every canonical child branch inside the Zhao
cut-forest components.  Marking them prevents a hierarchy segment from
mixing two branches which receive different matching allocations. -/
def zhaoBranchRootVertices
    {T : SimpleGraph V} [DecidableRel T.Adj] {globalRoot : V} {small : ℕ}
    (P : ZhaoForestPartition T globalRoot small) : Finset V :=
  Finset.univ.image fun j ↦
    P.fromOrderedForestVertex
      ((branchVertexEquiv P.orderedForest j
        ((toOrderedBranchForest P.orderedForest).branches.root j)).1)

/-- Literal mark set used by the whole-tree allocation: every component
root, every canonical child/branch root inside a component, and the optional
parent vertices which must move to the cluster layer in Lemma 6.3 Part 2. -/
def zhaoMarkedVertices
    {T : SimpleGraph V} [DecidableRel T.Adj] {globalRoot : V} {small : ℕ}
    (P : ZhaoForestPartition T globalRoot small)
    (optionalParents : Finset V) : Finset V :=
  Finset.univ.image P.roots ∪ zhaoBranchRootVertices P ∪ optionalParents

/-- Branch-coordinate version of `zhaoMarkedVertices`, ready for
`SpecialSegmentation`.  The global root is automatically discarded by
`branchSpecial`. -/
def zhaoSpecialCoordinates
    {T : SimpleGraph V} [DecidableRel T.Adj] {globalRoot : V} {small : ℕ}
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optionalParents : Finset V) :
    Finset (WholeBranchVertex T hT globalRoot) :=
  wholeSpecialCoordinates T hT globalRoot
    (zhaoMarkedVertices P optionalParents)

/-- The marked hierarchy whose graph still contains every edge of `T`. -/
abbrev wholeHierarchy
    (T : SimpleGraph V) (hT : T.IsTree) (root : V)
    (special : Finset (WholeBranchVertex T hT root)) :=
  toHierarchicalSegmentForest (wholeBranchForest T hT root) special

/-- Literal source vertex represented by a coordinate of the marked
whole-tree hierarchy.  This is the classifier used to decide whether a
segment belongs to selected `F₀`, residual `F₁`, or `F_b`. -/
def wholeHierarchyOriginalVertex
    (T : SimpleGraph V) (hT : T.IsTree) (root : V)
    (special : Finset (WholeBranchVertex T hT root)) :
    (wholeHierarchy T hT root special).Vertex → V :=
  fun x ↦ fromSingleCoordinate T hT root
    ((branchGraphIso (wholeOrderedTree T hT root))
      (flatten (wholeBranchForest T hT root) special x))

/-- Coordinate of a literal source vertex in the marked whole-tree
hierarchy.  This is the inverse coordinate map to
`wholeHierarchyOriginalVertex`, used to retain exact placement information
after transporting the hierarchical copy back to `T`. -/
def toWholeHierarchyVertex
    (T : SimpleGraph V) (hT : T.IsTree) (root : V)
    (special : Finset (WholeBranchVertex T hT root)) :
    V → (wholeHierarchy T hT root special).Vertex :=
  fun x ↦ unflatten (wholeBranchForest T hT root) special
    (toWholeBranchForestVertex T hT root x)

@[simp] theorem wholeHierarchyOriginal_toWholeHierarchyVertex
    (T : SimpleGraph V) (hT : T.IsTree) (root : V)
    (special : Finset (WholeBranchVertex T hT root)) (x : V) :
    wholeHierarchyOriginalVertex T hT root special
      (toWholeHierarchyVertex T hT root special x) = x := by
  rw [wholeHierarchyOriginalVertex, toWholeHierarchyVertex,
    flatten_unflatten, toWholeBranchForestVertex,
    (branchGraphIso (wholeOrderedTree T hT root)).apply_symm_apply,
    from_toSingleCoordinate]

theorem toWholeHierarchyVertex_injective
    (T : SimpleGraph V) (hT : T.IsTree) (root : V)
    (special : Finset (WholeBranchVertex T hT root)) :
    Function.Injective (toWholeHierarchyVertex T hT root special) := by
  intro x y hxy
  simpa only [wholeHierarchyOriginal_toWholeHierarchyVertex] using
    congrArg (wholeHierarchyOriginalVertex T hT root special) hxy

/-- Placement-preserving form of the full-tree conclusion.  The retained
`specialEmbedding` exposes every hierarchy root/interior candidate
membership, while `fullCopy` is a copy of the literal input tree. -/
structure FullTreeRegularEmbedding
    (T : SimpleGraph V) (hT : T.IsTree) (globalRoot : V)
    (special : Finset (WholeBranchVertex T hT globalRoot))
    (G : SimpleGraph B)
    (globalRootImage : Fin 1 → B)
    (rootCandidate :
      Fin (marks (wholeBranchForest T hT globalRoot) special).card → Finset B)
    (interiorCandidate :
      (i : Fin (marks (wholeBranchForest T hT globalRoot) special).card) →
        Fin ((wholeHierarchy T hT globalRoot special).segments.size i) →
        Finset B) where
  specialEmbedding : SpecialRegularEmbedding
    (wholeBranchForest T hT globalRoot) special G globalRootImage
      rootCandidate interiorCandidate
  fullCopy : T.Copy G
  fullCopy_apply : ∀ x,
    fullCopy x = specialEmbedding.hierarchyEmbedding.fullCopy
      (toWholeHierarchyVertex T hT globalRoot special x)

theorem FullTreeRegularEmbedding.map_globalRoot
    (T : SimpleGraph V) (hT : T.IsTree) (globalRoot : V)
    (special : Finset (WholeBranchVertex T hT globalRoot))
    (G : SimpleGraph B) (globalRootImage : Fin 1 → B)
    (rootCandidate :
      Fin (marks (wholeBranchForest T hT globalRoot) special).card → Finset B)
    (interiorCandidate :
      (i : Fin (marks (wholeBranchForest T hT globalRoot) special).card) →
        Fin ((wholeHierarchy T hT globalRoot special).segments.size i) →
        Finset B)
    (E : FullTreeRegularEmbedding T hT globalRoot special G
      globalRootImage rootCandidate interiorCandidate) :
    E.fullCopy globalRoot = globalRootImage 0 := by
  rw [E.fullCopy_apply]
  change E.specialEmbedding.hierarchyEmbedding.fullCopy
    (unflatten (wholeBranchForest T hT globalRoot) special
      (toWholeBranchForestVertex T hT globalRoot globalRoot)) = _
  rw [toWholeBranchForestVertex_root]
  exact E.specialEmbedding.hierarchyEmbedding.fullCopy_root 0

/-- Every requested non-global mark is realized in a hierarchy-root
candidate.  This is the placement statement used to retain future leaf
parents in the large host layer. -/
theorem FullTreeRegularEmbedding.map_markedVertex_eq_segmentRoot
    (T : SimpleGraph V) (hT : T.IsTree) (globalRoot : V)
    (markedVertices : Finset V)
    (G : SimpleGraph B) (globalRootImage : Fin 1 → B)
    (rootCandidate : Fin
      (marks (wholeBranchForest T hT globalRoot)
        (wholeSpecialCoordinates T hT globalRoot markedVertices)).card → Finset B)
    (interiorCandidate :
      (i : Fin
        (marks (wholeBranchForest T hT globalRoot)
          (wholeSpecialCoordinates T hT globalRoot markedVertices)).card) →
        Fin ((wholeHierarchy T hT globalRoot
          (wholeSpecialCoordinates T hT globalRoot markedVertices)).segments.size i) →
        Finset B)
    (E : FullTreeRegularEmbedding T hT globalRoot
      (wholeSpecialCoordinates T hT globalRoot markedVertices) G
      globalRootImage rootCandidate interiorCandidate)
    (x : V) (hx : x ∈ markedVertices) (hxRoot : x ≠ globalRoot) :
    ∃ i,
      toWholeHierarchyVertex T hT globalRoot
        (wholeSpecialCoordinates T hT globalRoot markedVertices) x =
          (wholeHierarchy T hT globalRoot
            (wholeSpecialCoordinates T hT globalRoot markedVertices)).segmentRoot i ∧
      E.fullCopy x ∈ rootCandidate i := by
  classical
  let F := wholeBranchForest T hT globalRoot
  let rawSpecial :=
    markedVertices.image (toWholeBranchForestVertex T hT globalRoot)
  have hxImage : toWholeBranchForestVertex T hT globalRoot x ∈ rawSpecial :=
    Finset.mem_image.mpr ⟨x, hx, rfl⟩
  cases hcoord : toWholeBranchForestVertex T hT globalRoot x with
  | inl q =>
      have hq : q = 0 := Subsingleton.elim _ _
      have hxr : x = globalRoot := by
        apply toWholeBranchForestVertex_injective T hT globalRoot
        rw [hcoord, hq, toWholeBranchForestVertex_root]
      exact False.elim (hxRoot hxr)
  | inr z =>
      have hz : (Sum.inr z : F.Vertex) ∈ rawSpecial := by
        change (Sum.inr z : F.Vertex) ∈ rawSpecial
        rw [← hcoord]
        exact hxImage
      obtain ⟨i, hi⟩ := unflatten_branchSpecial_is_segmentRoot
        F rawSpecial z hz
      let i' : Fin
          (marks (wholeBranchForest T hT globalRoot)
            (wholeSpecialCoordinates T hT globalRoot markedVertices)).card :=
        ⟨i.val, by
          simpa [F, rawSpecial, wholeSpecialCoordinates] using i.isLt⟩
      have hi' :
          toWholeHierarchyVertex T hT globalRoot
              (wholeSpecialCoordinates T hT globalRoot markedVertices) x =
            (wholeHierarchy T hT globalRoot
              (wholeSpecialCoordinates T hT globalRoot markedVertices)).segmentRoot i' := by
        change unflatten F (branchSpecial F rawSpecial)
            (toWholeBranchForestVertex T hT globalRoot x) =
          (toHierarchicalSegmentForest F (branchSpecial F rawSpecial)).segmentRoot i'
        rw [hcoord]
        have hii : i' = i := Fin.ext rfl
        rw [hii]
        exact hi
      refine ⟨i', hi', ?_⟩
      rw [E.fullCopy_apply, hi']
      rw [Erdos547b.ZhaoLemma59Hierarchical.HierarchicalSegmentForest.segmentRoot,
        E.specialEmbedding.hierarchyEmbedding.fullCopy_segment,
        E.specialEmbedding.hierarchyEmbedding.map_root]
      exact E.specialEmbedding.hierarchyEmbedding.root_mem i'

theorem FullTreeRegularEmbedding.map_markedVertex
    (T : SimpleGraph V) (hT : T.IsTree) (globalRoot : V)
    (markedVertices : Finset V)
    (G : SimpleGraph B) (globalRootImage : Fin 1 → B)
    (rootCandidate : Fin
      (marks (wholeBranchForest T hT globalRoot)
        (wholeSpecialCoordinates T hT globalRoot markedVertices)).card → Finset B)
    (interiorCandidate :
      (i : Fin
        (marks (wholeBranchForest T hT globalRoot)
          (wholeSpecialCoordinates T hT globalRoot markedVertices)).card) →
        Fin ((wholeHierarchy T hT globalRoot
          (wholeSpecialCoordinates T hT globalRoot markedVertices)).segments.size i) →
        Finset B)
    (E : FullTreeRegularEmbedding T hT globalRoot
      (wholeSpecialCoordinates T hT globalRoot markedVertices) G
      globalRootImage rootCandidate interiorCandidate)
    (x : V) (hx : x ∈ markedVertices) (hxRoot : x ≠ globalRoot) :
    ∃ i, E.fullCopy x ∈ rootCandidate i := by
  obtain ⟨i, -, hi⟩ := E.map_markedVertex_eq_segmentRoot T hT globalRoot
    markedVertices G globalRootImage rootCandidate interiorCandidate x hx hxRoot
  exact ⟨i, hi⟩

/-- Full-tree realization retaining both the candidate-placement witness and
the literal copy.  No source copy or deleted-edge adjacency is an input. -/
theorem exists_fullTreeRegularEmbedding_of_cleanedRegularSystem
    {c k : ℕ}
    (T : SimpleGraph V) (hT : T.IsTree) (globalRoot : V)
    (special : Finset (WholeBranchVertex T hT globalRoot))
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ)
    (globalRootImage : Fin 1 → B)
    (rootGroup : Fin (marks (wholeBranchForest T hT globalRoot) special).card → Fin c)
    (group : Fin (marks (wholeBranchForest T hT globalRoot) special).card → Fin k)
    (rootCandidate :
      Fin (marks (wholeBranchForest T hT globalRoot) special).card → Finset B)
    (interiorCandidate :
      (i : Fin (marks (wholeBranchForest T hT globalRoot) special).card) →
        Fin ((wholeHierarchy T hT globalRoot special).segments.size i) →
        Finset B)
    (S : CleanedRegularSystem
        (wholeHierarchy T hT globalRoot special) G rho globalRootImage
        rootGroup group rootCandidate interiorCandidate) :
    Nonempty (FullTreeRegularEmbedding T hT globalRoot special G
      globalRootImage rootCandidate interiorCandidate) := by
  obtain ⟨E⟩ := exists_specialRegularEmbedding
    (wholeBranchForest T hT globalRoot) special G rho globalRootImage
      rootGroup group rootCandidate interiorCandidate S
  let orderedCopy : (wholeOrderedTree T hT globalRoot).graph.Copy G :=
    copyOfBranchForestCopy (wholeOrderedTree T hT globalRoot) G E.originalCopy
  let fullCopy : T.Copy G :=
    copyOfSingleOrderedCopy T hT globalRoot G orderedCopy
  refine ⟨
    { specialEmbedding := E
      fullCopy := fullCopy
      fullCopy_apply := ?_ }⟩
  intro x
  change E.originalCopy (toWholeBranchForestVertex T hT globalRoot x) =
    E.hierarchyEmbedding.fullCopy
      (unflatten (wholeBranchForest T hT globalRoot) special
        (toWholeBranchForestVertex T hT globalRoot x))
  exact E.originalCopy_apply _

/-- Full-tree, no-link conclusion used by Lemma 6.14 Part 2 and by the
Claim-6.17 switch.  All parent edges are realized by the hierarchical online
constructor before any graph transport occurs. -/
theorem exists_fullTreeCopy_of_cleanedRegularSystem
    {c k : ℕ}
    (T : SimpleGraph V) (hT : T.IsTree) (globalRoot : V)
    (special : Finset (WholeBranchVertex T hT globalRoot))
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ)
    (globalRootImage : Fin 1 → B)
    (rootGroup : Fin (marks (wholeBranchForest T hT globalRoot) special).card → Fin c)
    (group : Fin (marks (wholeBranchForest T hT globalRoot) special).card → Fin k)
    (rootCandidate :
      Fin (marks (wholeBranchForest T hT globalRoot) special).card → Finset B)
    (interiorCandidate :
      (i : Fin (marks (wholeBranchForest T hT globalRoot) special).card) →
        Fin ((wholeHierarchy T hT globalRoot special).segments.size i) →
        Finset B)
    (S : CleanedRegularSystem
        (wholeHierarchy T hT globalRoot special) G rho globalRootImage
        rootGroup group rootCandidate interiorCandidate) :
    Nonempty (T.Copy G) := by
  obtain ⟨E⟩ := exists_fullTreeRegularEmbedding_of_cleanedRegularSystem
    T hT globalRoot special G rho globalRootImage rootGroup group
      rootCandidate interiorCandidate S
  exact ⟨E.fullCopy⟩

/-- Containment spelling for the stability contradiction. -/
theorem isContained_of_cleanedRegularSystem
    {c k : ℕ}
    (T : SimpleGraph V) (hT : T.IsTree) (globalRoot : V)
    (special : Finset (WholeBranchVertex T hT globalRoot))
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ)
    (globalRootImage : Fin 1 → B)
    (rootGroup : Fin (marks (wholeBranchForest T hT globalRoot) special).card → Fin c)
    (group : Fin (marks (wholeBranchForest T hT globalRoot) special).card → Fin k)
    (rootCandidate :
      Fin (marks (wholeBranchForest T hT globalRoot) special).card → Finset B)
    (interiorCandidate :
      (i : Fin (marks (wholeBranchForest T hT globalRoot) special).card) →
        Fin ((wholeHierarchy T hT globalRoot special).segments.size i) →
        Finset B)
    (S : CleanedRegularSystem
        (wholeHierarchy T hT globalRoot special) G rho globalRootImage
        rootGroup group rootCandidate interiorCandidate) :
    T.IsContained G := by
  exact (exists_fullTreeCopy_of_cleanedRegularSystem T hT globalRoot special G
    rho globalRootImage rootGroup group rootCandidate interiorCandidate S).some.isContained

/-- Literal-vertex spelling used by the Zhao partition adapters.  In the
Lemma-6.14 application `markedVertices` is the union of all non-initial Zhao
roots with the optional parent-vertex set selected by Lemma 6.3. -/
theorem exists_fullTreeCopy_of_markedVertices_cleanedRegularSystem
    {c k : ℕ}
    (T : SimpleGraph V) (hT : T.IsTree) (globalRoot : V)
    (markedVertices : Finset V)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ)
    (globalRootImage : Fin 1 → B)
    (rootGroup : Fin
      (marks (wholeBranchForest T hT globalRoot)
        (wholeSpecialCoordinates T hT globalRoot markedVertices)).card → Fin c)
    (group : Fin
      (marks (wholeBranchForest T hT globalRoot)
        (wholeSpecialCoordinates T hT globalRoot markedVertices)).card → Fin k)
    (rootCandidate : Fin
      (marks (wholeBranchForest T hT globalRoot)
        (wholeSpecialCoordinates T hT globalRoot markedVertices)).card → Finset B)
    (interiorCandidate :
      (i : Fin
        (marks (wholeBranchForest T hT globalRoot)
          (wholeSpecialCoordinates T hT globalRoot markedVertices)).card) →
        Fin ((wholeHierarchy T hT globalRoot
          (wholeSpecialCoordinates T hT globalRoot markedVertices)).segments.size i) →
        Finset B)
    (S : CleanedRegularSystem
        (wholeHierarchy T hT globalRoot
          (wholeSpecialCoordinates T hT globalRoot markedVertices))
        G rho globalRootImage rootGroup group rootCandidate interiorCandidate) :
    Nonempty (T.Copy G) := by
  exact exists_fullTreeCopy_of_cleanedRegularSystem T hT globalRoot
    (wholeSpecialCoordinates T hT globalRoot markedVertices) G rho
      globalRootImage rootGroup group rootCandidate interiorCandidate S

end Erdos547b.ZhaoLemma614HierarchicalFullTree

#print axioms Erdos547b.ZhaoLemma614HierarchicalFullTree.exists_fullTreeCopy_of_cleanedRegularSystem
#print axioms Erdos547b.ZhaoLemma614HierarchicalFullTree.exists_fullTreeRegularEmbedding_of_cleanedRegularSystem
#print axioms Erdos547b.ZhaoLemma614HierarchicalFullTree.isContained_of_cleanedRegularSystem
#print axioms Erdos547b.ZhaoLemma614HierarchicalFullTree.exists_fullTreeCopy_of_markedVertices_cleanedRegularSystem
