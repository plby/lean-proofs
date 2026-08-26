/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim68BranchAdapter

/-!
# Graph transport for the canonical root-branch decomposition

`toOrderedBranchForest` is not only a family of correctly sized rooted
trees.  Its reconstructed graph is canonically isomorphic to the original
ordered rooted forest.  This module records that missing transport, needed
to run the arbitrary-special hierarchy on a one-root reindexing of the full
tree and then transport the resulting copy back.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoClaim68BranchGraphTransport

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoClaim68BranchAdapter
open SimpleGraphRose547

universe u

variable {r : ℕ}

/-- Forget the branch coordinates.  A reconstructed root goes to the
corresponding component root, and a branch coordinate goes to the vertex of
the canonical descendant set which it numbers. -/
def flattenBranch (F : OrderedRootedForest r) :
    (toOrderedBranchForest F).Vertex → (ForestVertex F)
  | Sum.inl i => ⟨i, F.root i⟩
  | Sum.inr z => (branchCoordinatesEquivNonroots F z).1

@[simp] theorem flattenBranch_root (F : OrderedRootedForest r) (i : Fin r) :
    flattenBranch F (Sum.inl i) = ⟨i, F.root i⟩ := rfl

@[simp] theorem flattenBranch_branch (F : OrderedRootedForest r)
    (z : Σ j, Fin ((toOrderedBranchForest F).branches.size j)) :
    flattenBranch F (Sum.inr z) = (branchCoordinatesEquivNonroots F z).1 := rfl

@[simp] theorem flattenBranch_branch_vertex (F : OrderedRootedForest r)
    (z : Σ j, Fin ((toOrderedBranchForest F).branches.size j)) :
    flattenBranch F (Sum.inr z) = (branchVertexEquiv F z.1 z.2).1 := rfl

theorem flattenBranch_injective (F : OrderedRootedForest r) :
    Function.Injective (flattenBranch F) := by
  classical
  let IsRoot : ForestVertex F → Prop := fun q ↦ q.2 = F.root q.1
  rintro (i | z) (k | w) h
  · exact congrArg Sum.inl (congrArg Sigma.fst h)
  · exfalso
    have hn := (branchCoordinatesEquivNonroots F w).2
    apply hn
    have hi : IsRoot ⟨i, F.root i⟩ := rfl
    exact Eq.mp (congrArg IsRoot h) hi
  · exfalso
    have hn := (branchCoordinatesEquivNonroots F z).2
    apply hn
    have hk : IsRoot ⟨k, F.root k⟩ := rfl
    exact Eq.mp (congrArg IsRoot h).symm hk
  · apply congrArg Sum.inr
    apply (branchCoordinatesEquivNonroots F).injective
    exact Subtype.ext h

theorem flattenBranch_surjective (F : OrderedRootedForest r) :
    Function.Surjective (flattenBranch F) := by
  classical
  rintro z
  rcases z with ⟨i, a⟩
  by_cases ha : a = F.root i
  · subst a
    exact ⟨Sum.inl i, rfl⟩
  · let q : NonRootCoordinate F := ⟨⟨i, a⟩, ha⟩
    let x := (branchCoordinatesEquivNonroots F).symm q
    refine ⟨Sum.inr x, ?_⟩
    change ((branchCoordinatesEquivNonroots F) x).1 = ⟨i, a⟩
    rw [Equiv.apply_symm_apply]

/-- The canonical vertex equivalence underlying the branch decomposition. -/
def branchEquiv (F : OrderedRootedForest r) :
    (toOrderedBranchForest F).Vertex ≃ ForestVertex F :=
  Equiv.ofBijective (flattenBranch F)
    ⟨flattenBranch_injective F, flattenBranch_surjective F⟩

@[simp] theorem branchEquiv_apply (F : OrderedRootedForest r)
    (x : (toOrderedBranchForest F).Vertex) :
    branchEquiv F x = flattenBranch F x := rfl

theorem orderedGraph_adj_mk (F : OrderedRootedForest r)
    {i j : Fin r} {a : Fin (F.size i)} {b : Fin (F.size j)} :
    F.graph.Adj (Sigma.mk i a) (Sigma.mk j b) ↔
      ∃ h : i = j, (F.tree i).Adj a (h ▸ b) := by
  constructor
  · intro hab
    rcases (Erdos547b.RegularPair.OrderedRootedForest.graph_adj _ _).mp hab with
      ⟨q, c, d, hleft, hright, hcd⟩
    cases hleft
    cases hright
    exact ⟨rfl, hcd⟩
  · rintro ⟨rfl, hab⟩
    exact (Erdos547b.RegularPair.OrderedRootedForest.graph_adj _ _).mpr
      ⟨i, a, b, rfl, rfl, hab⟩

/-- An adjacent vertex different from the global root cannot leave the
rooted branch containing its neighbor.  This includes the boundary case in
which the first vertex is itself the child defining the branch. -/
theorem adj_mem_rootedBranch_of_mem_of_ne_root
    {A : Type*} [Fintype A] [DecidableEq A]
    {T : SimpleGraph A} (hT : T.IsTree) {root child u v : A}
    (hchild : IsChild T root root child)
    (hu : u ∈ rootedDescendants T root child)
    (hv : v ≠ root) (huv : T.Adj u v) :
    v ∈ rootedDescendants T root child := by
  by_cases huc : u = child
  · subst u
    rw [mem_rootedDescendants]
    have hrc : T.dist root child = 1 :=
      T.dist_eq_one_iff_adj.mpr hchild.1
    have hcv : T.dist child v = 1 := T.dist_eq_one_iff_adj.mpr huv
    rcases hT.dist_eq_dist_add_one_of_adj root huv with hback | hforward
    · have hv0 : T.dist root v = 0 := by omega
      exact False.elim (hv (hT.connected.dist_eq_zero_iff.mp hv0).symm)
    · omega
  · exact adj_mem_rootedDescendants_of_mem_of_ne hT hu huc huv

/-- Original local vertex represented by one numbered branch coordinate. -/
def branchLocalVertex (F : OrderedRootedForest r)
    (j : Fin (Fintype.card (ChildKey F)))
    (a : Fin ((toOrderedBranchForest F).branches.size j)) :
    Fin (F.size (childKeyEquiv F j).1.1) :=
  ((branchSetEquiv F j).symm (branchVertexEquiv F j a)).1

theorem branchLocalVertex_mem (F : OrderedRootedForest r)
    (j : Fin (Fintype.card (ChildKey F)))
    (a : Fin ((toOrderedBranchForest F).branches.size j)) :
    branchLocalVertex F j a ∈ rootedDescendants
      (F.tree (childKeyEquiv F j).1.1)
      (F.root (childKeyEquiv F j).1.1)
      (childKeyEquiv F j).1.2 :=
  ((branchSetEquiv F j).symm (branchVertexEquiv F j a)).2

theorem branchLocalVertex_ne_componentRoot (F : OrderedRootedForest r)
    (j : Fin (Fintype.card (ChildKey F)))
    (a : Fin ((toOrderedBranchForest F).branches.size j)) :
    branchLocalVertex F j a ≠ F.root (childKeyEquiv F j).1.1 := by
  intro hroot
  apply root_not_mem_rootedDescendants_child
    (T := F.tree (childKeyEquiv F j).1.1)
    (r := F.root (childKeyEquiv F j).1.1)
    (x := F.root (childKeyEquiv F j).1.1)
    (y := (childKeyEquiv F j).1.2)
  · refine ⟨(childKeyEquiv F j).2, ?_⟩
    simpa only [SimpleGraph.dist_self, zero_add] using
      (F.tree _).dist_eq_one_iff_adj.mpr (childKeyEquiv F j).2
  · simpa only [hroot] using branchLocalVertex_mem F j a

theorem childKey_isChild (F : OrderedRootedForest r)
    (j : Fin (Fintype.card (ChildKey F))) :
    IsChild (F.tree (childKeyEquiv F j).1.1)
      (F.root (childKeyEquiv F j).1.1)
      (F.root (childKeyEquiv F j).1.1)
      (childKeyEquiv F j).1.2 := by
  refine ⟨(childKeyEquiv F j).2, ?_⟩
  simpa only [SimpleGraph.dist_self, zero_add] using
    (F.tree _).dist_eq_one_iff_adj.mpr (childKeyEquiv F j).2

@[simp] theorem branchLocalVertex_root (F : OrderedRootedForest r)
    (j : Fin (Fintype.card (ChildKey F))) :
    branchLocalVertex F j ((toOrderedBranchForest F).branches.root j) =
      (childKeyEquiv F j).1.2 := by
  rw [branchLocalVertex, branchVertexEquiv_root,
    Equiv.symm_apply_apply]

/-- `flattenBranch` is literally the component paired with the local vertex
of that branch. -/
theorem flattenBranch_branch_eq_local (F : OrderedRootedForest r)
    (j : Fin (Fintype.card (ChildKey F)))
    (a : Fin ((toOrderedBranchForest F).branches.size j)) :
    flattenBranch F (Sum.inr ⟨j, a⟩) =
      ⟨(childKeyEquiv F j).1.1, branchLocalVertex F j a⟩ := by
  have h := Equiv.apply_symm_apply (branchSetEquiv F j)
    (branchVertexEquiv F j a)
  exact (congrArg Subtype.val h).symm

/-- The local branch-tree adjacency is exactly adjacency of the corresponding
vertices in the original component tree. -/
theorem branchTree_adj_iff_local (F : OrderedRootedForest r)
    (j : Fin (Fintype.card (ChildKey F)))
    (a b : Fin ((toOrderedBranchForest F).branches.size j)) :
    ((toOrderedBranchForest F).branches.tree j).Adj a b ↔
      (F.tree (childKeyEquiv F j).1.1).Adj
        (branchLocalVertex F j a) (branchLocalVertex F j b) := by
  rfl

/-- A non-root neighbor of a vertex in a canonical branch remains in that
branch.  Keeping this statement on sigma vertices isolates all component
index transport in one place. -/
theorem adj_mem_branchSet_of_mem_of_ne_root (F : OrderedRootedForest r)
    (j : Fin (Fintype.card (ChildKey F)))
    {u v : ForestVertex F} (hu : u ∈ branchSet F j)
    (hv : v.2 ≠ F.root v.1) (huv : F.graph.Adj u v) :
    v ∈ branchSet F j := by
  classical
  rcases u with ⟨i, u⟩
  rcases v with ⟨k, v⟩
  rcases hu with ⟨hi, hi', hu⟩
  rcases (orderedGraph_adj_mk F).mp huv with ⟨hik, huv⟩
  cases hik
  cases hi
  have hhi : hi' = rfl := Subsingleton.elim _ _
  cases hhi
  have hu' : u ∈ rootedDescendants
      (F.tree (childKeyEquiv F j).1.1)
      (F.root (childKeyEquiv F j).1.1)
      (childKeyEquiv F j).1.2 := by
    simpa using hu
  have huv' : (F.tree (childKeyEquiv F j).1.1).Adj u v := by
    simpa using huv
  have hv' : v ≠ F.root (childKeyEquiv F j).1.1 := by
    simpa using hv
  refine ⟨rfl, ⟨rfl, ?_⟩⟩
  exact adj_mem_rootedBranch_of_mem_of_ne_root
    (F.isTree (childKeyEquiv F j).1.1)
    (childKey_isChild F j) hu' hv' huv'

/-- `flattenBranch` preserves every reconstructed branch edge. -/
theorem flattenBranch_map_adj (F : OrderedRootedForest r)
    {x y : (toOrderedBranchForest F).Vertex}
    (hxy : (toOrderedBranchForest F).graph.Adj x y) :
    F.graph.Adj (flattenBranch F x) (flattenBranch F y) := by
  classical
  rcases x with i | z <;> rcases y with k | w
  · exact False.elim hxy
  · rcases hxy with ⟨hown, hroot⟩
    rcases w with ⟨j, a⟩
    dsimp only at hroot
    subst a
    subst i
    rw [flattenBranch_branch_eq_local, branchLocalVertex_root]
    exact (orderedGraph_adj_mk F).mpr ⟨rfl, (childKeyEquiv F j).2⟩
  · rcases hxy with ⟨hown, hroot⟩
    rcases z with ⟨j, a⟩
    dsimp only at hroot
    subst a
    subst k
    rw [flattenBranch_branch_eq_local, branchLocalVertex_root]
    exact (orderedGraph_adj_mk F).mpr ⟨rfl, (childKeyEquiv F j).2.symm⟩
  · rcases hxy with ⟨hjk, hadj⟩
    rcases z with ⟨j, a⟩
    rcases w with ⟨l, c⟩
    dsimp only at hjk
    subst l
    rw [flattenBranch_branch_eq_local, flattenBranch_branch_eq_local]
    exact (orderedGraph_adj_mk F).mpr
      ⟨rfl, (branchTree_adj_iff_local F j a c).mp hadj⟩

/-- If the root is adjacent to a vertex in one of its canonical descendant
branches, that vertex is the child which roots the branch. -/
theorem branchCoordinate_eq_root_of_adj
    (F : OrderedRootedForest r)
    (j : Fin (Fintype.card (ChildKey F)))
    (a : Fin ((toOrderedBranchForest F).branches.size j))
    (hadj : F.graph.Adj
      ⟨(childKeyEquiv F j).1.1, F.root (childKeyEquiv F j).1.1⟩
      (flattenBranch F (Sum.inr ⟨j, a⟩))) :
    a = (toOrderedBranchForest F).branches.root j := by
  classical
  rw [flattenBranch_branch_eq_local] at hadj
  have hrootq : (F.tree (childKeyEquiv F j).1.1).Adj
      (F.root (childKeyEquiv F j).1.1) (branchLocalVertex F j a) := by
    rcases (orderedGraph_adj_mk F).mp hadj with ⟨hidx, h⟩
    have hh : hidx = rfl := Subsingleton.elim _ _
    cases hh
    exact h
  have hchildDist : (F.tree (childKeyEquiv F j).1.1).dist
      (F.root (childKeyEquiv F j).1.1) (childKeyEquiv F j).1.2 = 1 :=
    (F.tree _).dist_eq_one_iff_adj.mpr (childKeyEquiv F j).2
  have hqDist : (F.tree (childKeyEquiv F j).1.1).dist
      (F.root (childKeyEquiv F j).1.1) (branchLocalVertex F j a) = 1 :=
    (F.tree _).dist_eq_one_iff_adj.mpr hrootq
  have hchildq : (F.tree (childKeyEquiv F j).1.1).dist
      (childKeyEquiv F j).1.2 (branchLocalVertex F j a) = 0 := by
    have := mem_rootedDescendants.mp (branchLocalVertex_mem F j a)
    omega
  have heq : branchLocalVertex F j a = (childKeyEquiv F j).1.2 := by
    exact ((F.isTree (childKeyEquiv F j).1.1).connected.dist_eq_zero_iff.mp
      hchildq).symm
  let e := (branchCoordinateEquiv F j).trans (branchSetEquiv F j).symm
  apply e.injective
  apply Subtype.ext
  change branchLocalVertex F j a =
    branchLocalVertex F j ((toOrderedBranchForest F).branches.root j)
  simpa only [branchLocalVertex_root] using heq

/-- `flattenBranch` also reflects adjacency.  Hence the branch
reconstruction is the same graph, not merely a spanning subgraph. -/
theorem flattenBranch_reflect_adj (F : OrderedRootedForest r)
    {x y : (toOrderedBranchForest F).Vertex}
    (hxy : F.graph.Adj (flattenBranch F x) (flattenBranch F y)) :
    (toOrderedBranchForest F).graph.Adj x y := by
  classical
  rcases x with i | z <;> rcases y with k | w
  · have h := (orderedGraph_adj_mk F).mp hxy
    obtain ⟨hik, hadj⟩ := h
    subst k
    exact False.elim ((F.tree i).loopless.irrefl _ hadj)
  · rcases w with ⟨j, a⟩
    have hcomp : (childKeyEquiv F j).1.1 = i := by
      have h := (orderedGraph_adj_mk F).mp hxy
      obtain ⟨hi, _⟩ := h
      exact (branchCoordinatesEquivNonroots_component F j a).symm.trans hi.symm
    have ha : a = (toOrderedBranchForest F).branches.root j := by
      apply branchCoordinate_eq_root_of_adj F j a
      cases hcomp
      exact hxy
    refine ⟨?_, ha⟩
    change (childKeyEquiv F j).1.1 = i
    exact hcomp
  · rcases z with ⟨j, a⟩
    have hcomp : (childKeyEquiv F j).1.1 = k := by
      have h := (orderedGraph_adj_mk F).mp hxy.symm
      obtain ⟨hk, _⟩ := h
      exact (branchCoordinatesEquivNonroots_component F j a).symm.trans hk.symm
    have ha : a = (toOrderedBranchForest F).branches.root j := by
      apply branchCoordinate_eq_root_of_adj F j a
      cases hcomp
      exact hxy.symm
    refine ⟨?_, ha⟩
    change (childKeyEquiv F j).1.1 = k
    exact hcomp
  · rcases z with ⟨j, a⟩
    rcases w with ⟨l, c⟩
    let za := (branchVertexEquiv F j a).1
    let wc := (branchVertexEquiv F l c).1
    have hza : za ∈ branchSet F j := (branchVertexEquiv F j a).2
    have hwc : wc ∈ branchSet F l := (branchVertexEquiv F l c).2
    change F.graph.Adj za wc at hxy
    have hwRoot : wc.2 ≠ F.root wc.1 := by
      intro hw
      have : (⟨wc.1, F.root wc.1⟩ : ForestVertex F) ∈ branchSet F l := by
        have hwEq : wc = (⟨wc.1, F.root wc.1⟩ : ForestVertex F) :=
          Sigma.ext rfl (heq_of_eq hw)
        exact hwEq ▸ hwc
      exact anyRoot_not_mem_branchSet F wc.1 l this
    have hwInJ : wc ∈ branchSet F j :=
      adj_mem_branchSet_of_mem_of_ne_root F j hza hwRoot hxy
    have hjl : j = l := by
      by_contra hne
      exact (Set.disjoint_left.mp (branchSet_disjoint F hne)) hwInJ hwc
    subst l
    refine ⟨rfl, ?_⟩
    apply (branchTree_adj_iff_local F j a c).mpr
    have hGraph : F.graph.Adj
        (flattenBranch F (Sum.inr ⟨j, a⟩))
        (flattenBranch F (Sum.inr ⟨j, c⟩)) := by
      rw [flattenBranch_branch_vertex, flattenBranch_branch_vertex]
      exact hxy
    rw [flattenBranch_branch_eq_local,
      flattenBranch_branch_eq_local] at hGraph
    rcases (orderedGraph_adj_mk F).mp hGraph with ⟨hidx, hlocal⟩
    have hh : hidx = rfl := Subsingleton.elim _ _
    cases hh
    exact hlocal

/-- Canonical graph isomorphism between an ordered rooted forest and its
root-branch reconstruction. -/
def branchGraphIso (F : OrderedRootedForest r) :
    (toOrderedBranchForest F).graph ≃g F.graph where
  toEquiv := branchEquiv F
  map_rel_iff' := by
    intro x y
    exact ⟨flattenBranch_reflect_adj F, flattenBranch_map_adj F⟩

/-! ## Root-distance and parent transport -/

/-- Graph isomorphisms preserve distance between reachable vertices. -/
theorem graphIso_dist_eq_of_reachable
    {A C : Type*} {G : SimpleGraph A} {H : SimpleGraph C}
    (e : G ≃g H) {x y : A} (hxy : G.Reachable x y) :
    H.dist (e x) (e y) = G.dist x y := by
  have hmap : H.Reachable (e x) (e y) :=
    SimpleGraph.Iso.reachable_iff.mpr hxy
  obtain ⟨p, hp⟩ := hxy.exists_walk_length_eq_dist
  obtain ⟨q, hq⟩ := hmap.exists_walk_length_eq_dist
  have hforward : H.dist (e x) (e y) ≤ G.dist x y := by
    rw [← hp]
    have hle := H.dist_le (p.map e.toHom)
    change H.dist (e x) (e y) ≤ (p.map e.toHom).length at hle
    simpa only [SimpleGraph.Walk.length_map] using hle
  have hback : G.dist x y ≤ H.dist (e x) (e y) := by
    rw [← hq]
    have hle := G.dist_le (q.map e.symm.toHom)
    change G.dist (e.symm (e x)) (e.symm (e y)) ≤
      (q.map e.symm.toHom).length at hle
    simpa only [e.symm_apply_apply, SimpleGraph.Walk.length_map] using hle
  omega

/-- In a tree, a connected induced subtree has the same distance as the
ambient tree.  Its shortest path maps to the unique ambient path. -/
theorem induce_dist_eq_of_tree_of_connected
    {A : Type*} {T : SimpleGraph A} (hT : T.IsTree)
    (S : Set A) (hS : (T.induce S).Connected) (x y : S) :
    (T.induce S).dist x y = T.dist x y := by
  obtain ⟨p, hpPath, hpLength⟩ := hS.exists_path_of_dist x y
  obtain ⟨q, hqPath, hqLength⟩ :=
    hT.connected.exists_path_of_dist x.1 y.1
  let e : T.induce S ↪g T := SimpleGraph.Embedding.induce S
  have hpMapPath : (p.map e.toHom).IsPath :=
    SimpleGraph.Walk.map_isPath_of_injective e.injective hpPath
  have hpEq : p.map e.toHom = q :=
    (hT.existsUnique_path x.1 y.1).unique hpMapPath hqPath
  have hlen := congrArg SimpleGraph.Walk.length hpEq
  calc
    (T.induce S).dist x y = p.length := hpLength.symm
    _ = (p.map e.toHom).length := by
      rw [SimpleGraph.Walk.length_map]
    _ = q.length := hlen
    _ = T.dist x.1 y.1 := hqLength

/-- Distance in a numbered local branch is the ambient component-tree
distance from the child which roots that branch. -/
theorem branchTree_dist_eq_component_dist (F : OrderedRootedForest r)
    (j : Fin (Fintype.card (ChildKey F)))
    (a : Fin ((toOrderedBranchForest F).branches.size j)) :
    ((toOrderedBranchForest F).branches.tree j).dist
        ((toOrderedBranchForest F).branches.root j) a =
      (F.tree (childKeyEquiv F j).1.1).dist
        (childKeyEquiv F j).1.2 (branchLocalVertex F j a) := by
  let e := (branchCoordinateEquiv F j).trans (branchSetEquiv F j).symm
  have hReach :
      ((toOrderedBranchForest F).branches.tree j).Reachable
        ((toOrderedBranchForest F).branches.root j) a :=
    (toOrderedBranchForest F).branches.isTree j |>.connected _ _
  have hIso := graphIso_dist_eq_of_reachable
    (SimpleGraph.Iso.comap e (branchLocalGraph F j)) hReach
  have heRoot : e ((toOrderedBranchForest F).branches.root j) =
      ⟨(childKeyEquiv F j).1.2,
        self_mem_rootedDescendants _ _ _⟩ := by
    apply Subtype.ext
    exact branchLocalVertex_root F j
  have hInduce := induce_dist_eq_of_tree_of_connected
    (F.isTree (childKeyEquiv F j).1.1)
    (rootedDescendants
      (F.tree (childKeyEquiv F j).1.1)
      (F.root (childKeyEquiv F j).1.1)
      (childKeyEquiv F j).1.2 : Set _)
    (connected_induce_rootedDescendants
      (F.isTree (childKeyEquiv F j).1.1)
      (F.root (childKeyEquiv F j).1.1)
      (childKeyEquiv F j).1.2)
    (e ((toOrderedBranchForest F).branches.root j)) (e a)
  calc
    ((toOrderedBranchForest F).branches.tree j).dist
        ((toOrderedBranchForest F).branches.root j) a =
        (branchLocalGraph F j).dist
          (e ((toOrderedBranchForest F).branches.root j)) (e a) := hIso.symm
    _ = (F.tree (childKeyEquiv F j).1.1).dist
          (e ((toOrderedBranchForest F).branches.root j)).1 (e a).1 := hInduce
    _ = (F.tree (childKeyEquiv F j).1.1).dist
          (childKeyEquiv F j).1.2 (branchLocalVertex F j a) := by
      rw [heRoot]
      rfl

/-- The abstract `level` of a reconstructed branch forest is the literal
root-distance in the original component tree. -/
theorem flattenBranch_level_eq_component_dist (F : OrderedRootedForest r)
    (x : (toOrderedBranchForest F).Vertex) :
    (toOrderedBranchForest F).level x =
      (F.tree (flattenBranch F x).1).dist
        (F.root (flattenBranch F x).1) (flattenBranch F x).2 := by
  rcases x with i | z
  · simp only [OrderedBranchForest.level, flattenBranch_root,
      SimpleGraph.dist_self]
  · rcases z with ⟨j, a⟩
    rw [OrderedBranchForest.level, flattenBranch_branch_eq_local,
      branchTree_dist_eq_component_dist]
    have hdesc := mem_rootedDescendants.mp (branchLocalVertex_mem F j a)
    have hchild : (F.tree (childKeyEquiv F j).1.1).dist
        (F.root (childKeyEquiv F j).1.1) (childKeyEquiv F j).1.2 = 1 :=
      (F.tree _).dist_eq_one_iff_adj.mpr (childKeyEquiv F j).2
    calc
      1 + (F.tree (childKeyEquiv F j).1.1).dist
          (childKeyEquiv F j).1.2 (branchLocalVertex F j a) =
          (F.tree (childKeyEquiv F j).1.1).dist
              (F.root (childKeyEquiv F j).1.1) (childKeyEquiv F j).1.2 +
            (F.tree (childKeyEquiv F j).1.1).dist
              (childKeyEquiv F j).1.2 (branchLocalVertex F j a) := by
        rw [hchild]
      _ = (F.tree (childKeyEquiv F j).1.1).dist
          (F.root (childKeyEquiv F j).1.1)
          (branchLocalVertex F j a) := hdesc.symm

/-- Parent-coordinate transport required by the whole-source boundary
classifier.  For every non-root coordinate inside a canonical branch, its
local rooted-tree parent flattens to the globally rooted parent in the
original component tree. -/
theorem flattenBranch_localParent (F : OrderedRootedForest r)
    (j : Fin (Fintype.card (ChildKey F)))
    (a : Fin ((toOrderedBranchForest F).branches.size j))
    (ha : a ≠ (toOrderedBranchForest F).branches.root j) :
    let p := TreePartition.parent
      ((toOrderedBranchForest F).branches.isTree j)
      ((toOrderedBranchForest F).branches.root j) ha
    flattenBranch F (Sum.inr ⟨j, p⟩) =
      ⟨(childKeyEquiv F j).1.1,
        TreePartition.parent (F.isTree (childKeyEquiv F j).1.1)
          (F.root (childKeyEquiv F j).1.1)
          (branchLocalVertex_ne_componentRoot F j a)⟩ := by
  classical
  dsimp only
  let p := TreePartition.parent
    ((toOrderedBranchForest F).branches.isTree j)
    ((toOrderedBranchForest F).branches.root j) ha
  have hlocalAdj : ((toOrderedBranchForest F).branches.tree j).Adj p a :=
    TreePartition.parent_adj
      ((toOrderedBranchForest F).branches.isTree j)
      ((toOrderedBranchForest F).branches.root j) ha
  have hambientAdj : (F.tree (childKeyEquiv F j).1.1).Adj
      (branchLocalVertex F j p) (branchLocalVertex F j a) := by
    have hGraph : F.graph.Adj
        (flattenBranch F (Sum.inr ⟨j, p⟩))
        (flattenBranch F (Sum.inr ⟨j, a⟩)) := by
      apply flattenBranch_map_adj F
      exact OrderedBranchForest.graph_adj_branch_branch
        (toOrderedBranchForest F) ⟨j, p⟩ ⟨j, a⟩ |>.mpr
          ⟨rfl, hlocalAdj⟩
    rw [flattenBranch_branch_eq_local, flattenBranch_branch_eq_local] at hGraph
    rcases (orderedGraph_adj_mk F).mp hGraph with ⟨hidx, hlocal⟩
    have hh : hidx = rfl := Subsingleton.elim _ _
    cases hh
    exact hlocal
  have hlocalDist := TreePartition.parent_dist_add_one
    ((toOrderedBranchForest F).branches.isTree j)
    ((toOrderedBranchForest F).branches.root j) ha
  have hlocalDist' :
      ((toOrderedBranchForest F).branches.tree j).dist
          ((toOrderedBranchForest F).branches.root j) p + 1 =
        ((toOrderedBranchForest F).branches.tree j).dist
          ((toOrderedBranchForest F).branches.root j) a := by
    simpa only [p] using hlocalDist
  have hpBranchDist := branchTree_dist_eq_component_dist F j p
  have haBranchDist := branchTree_dist_eq_component_dist F j a
  have hchildDist :
      (F.tree (childKeyEquiv F j).1.1).dist
          (childKeyEquiv F j).1.2 (branchLocalVertex F j p) + 1 =
        (F.tree (childKeyEquiv F j).1.1).dist
          (childKeyEquiv F j).1.2 (branchLocalVertex F j a) := by
    rw [← hpBranchDist, ← haBranchDist]
    exact hlocalDist'
  have hpDesc := mem_rootedDescendants.mp (branchLocalVertex_mem F j p)
  have haDesc := mem_rootedDescendants.mp (branchLocalVertex_mem F j a)
  have hambientDist :
      (F.tree (childKeyEquiv F j).1.1).dist
          (F.root (childKeyEquiv F j).1.1) (branchLocalVertex F j p) + 1 =
        (F.tree (childKeyEquiv F j).1.1).dist
          (F.root (childKeyEquiv F j).1.1) (branchLocalVertex F j a) := by
    omega
  rw [flattenBranch_branch_eq_local]
  have hparent : branchLocalVertex F j p =
      TreePartition.parent (F.isTree (childKeyEquiv F j).1.1)
        (F.root (childKeyEquiv F j).1.1)
        (branchLocalVertex_ne_componentRoot F j a) :=
    TreePartition.eq_parent_of_adj_of_dist_add_one
      (F.isTree (childKeyEquiv F j).1.1)
      (F.root (childKeyEquiv F j).1.1)
      (branchLocalVertex_ne_componentRoot F j a) hambientAdj hambientDist
  exact Sigma.ext rfl (heq_of_eq hparent)

/-- Transport a concrete branch-forest copy back to the ordered rooted
forest. -/
def copyOfBranchForestCopy
    {B : Type u} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest r) (G : SimpleGraph B)
    (C : (toOrderedBranchForest F).graph.Copy G) : F.graph.Copy G :=
  C.comp (branchGraphIso F).symm.toCopy

end Erdos547b.ZhaoClaim68BranchGraphTransport

#print axioms Erdos547b.ZhaoClaim68BranchGraphTransport.flattenBranch_injective
#print axioms Erdos547b.ZhaoClaim68BranchGraphTransport.flattenBranch_surjective
#print axioms Erdos547b.ZhaoClaim68BranchGraphTransport.flattenBranch_map_adj
#print axioms Erdos547b.ZhaoClaim68BranchGraphTransport.flattenBranch_reflect_adj
#print axioms Erdos547b.ZhaoClaim68BranchGraphTransport.flattenBranch_localParent
#print axioms Erdos547b.ZhaoClaim68BranchGraphTransport.copyOfBranchForestCopy
