/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.ForestCapacity

/-!
# A tree as a one-component ordered rooted forest

This is the outer reindexing used by the full-tree hierarchical form of
Lemma 6.14.  It has exactly one original root; after its root branches are
segmented at all Zhao component roots, every deleted root--parent edge is an
ordinary hierarchical attachment edge.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoSingleTreeOrderedForest

open Fintype SimpleGraph
open Erdos547b.RegularPair

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Canonical numbering of a finite vertex type. -/
def vertexEquiv : Fin (Fintype.card V) ≃ V :=
  (Fintype.equivFin V).symm

/-- A rooted tree, canonically reindexed as a one-component ordered rooted
forest. -/
def singleOrderedRootedTree (T : SimpleGraph V) (hT : T.IsTree) (root : V) :
    OrderedRootedForest 1 where
  size := fun _ ↦ Fintype.card V
  tree := fun _ ↦ T.comap (vertexEquiv (V := V))
  isTree := fun _ ↦ by
    exact (SimpleGraph.Iso.comap (vertexEquiv (V := V)) T).isTree_iff.mpr hT
  root := fun _ ↦ (vertexEquiv (V := V)).symm root

/-- The one-component sigma coordinate corresponding to an original
vertex. -/
def toSingleCoordinate (T : SimpleGraph V) (hT : T.IsTree) (root : V) :
    V → (Σ i, Fin ((singleOrderedRootedTree T hT root).size i)) :=
  fun x ↦ ⟨0, (vertexEquiv (V := V)).symm x⟩

/-- Forget the unique component index. -/
def fromSingleCoordinate (T : SimpleGraph V) (hT : T.IsTree) (root : V) :
    (Σ i, Fin ((singleOrderedRootedTree T hT root).size i)) → V :=
  fun z ↦ vertexEquiv z.2

@[simp] theorem from_toSingleCoordinate
    (T : SimpleGraph V) (hT : T.IsTree) (root x : V) :
    fromSingleCoordinate T hT root (toSingleCoordinate T hT root x) = x := by
  simp [fromSingleCoordinate, toSingleCoordinate, vertexEquiv]

@[simp] theorem toSingleCoordinate_injective
    (T : SimpleGraph V) (hT : T.IsTree) (root : V) :
    Function.Injective (toSingleCoordinate T hT root) := by
  intro x y hxy
  have hxy' := congrArg (fromSingleCoordinate T hT root) hxy
  simpa using hxy'

@[simp] theorem toSingleCoordinate_root
    (T : SimpleGraph V) (hT : T.IsTree) (root : V) :
    toSingleCoordinate T hT root root =
      ⟨0, (singleOrderedRootedTree T hT root).root 0⟩ := rfl

theorem toSingleCoordinate_map_adj
    (T : SimpleGraph V) (hT : T.IsTree) (root : V) {x y : V}
    (hxy : T.Adj x y) :
    (singleOrderedRootedTree T hT root).graph.Adj
      (toSingleCoordinate T hT root x)
      (toSingleCoordinate T hT root y) := by
  rw [OrderedRootedForest.graph_adj]
  refine ⟨0, (vertexEquiv (V := V)).symm x,
    (vertexEquiv (V := V)).symm y, rfl, rfl, ?_⟩
  simpa [singleOrderedRootedTree] using hxy

/-- Literal copy of the original tree in its one-component ordered
reindexing. -/
def toSingleCopy (T : SimpleGraph V) (hT : T.IsTree) (root : V) :
    T.Copy (singleOrderedRootedTree T hT root).graph where
  toHom :=
    { toFun := toSingleCoordinate T hT root
      map_rel' := fun hxy ↦ toSingleCoordinate_map_adj T hT root hxy }
  injective' := toSingleCoordinate_injective T hT root

/-- Transport a concrete copy of the one-component reindexing back to a
concrete copy of the literal input tree. -/
def copyOfSingleOrderedCopy
    {B : Type v} [Fintype B] [DecidableEq B]
    (T : SimpleGraph V) (hT : T.IsTree) (root : V)
    (G : SimpleGraph B)
    (C : (singleOrderedRootedTree T hT root).graph.Copy G) : T.Copy G :=
  C.comp (toSingleCopy T hT root)

end Erdos547b.ZhaoSingleTreeOrderedForest

#print axioms Erdos547b.ZhaoSingleTreeOrderedForest.toSingleCopy
#print axioms Erdos547b.ZhaoSingleTreeOrderedForest.copyOfSingleOrderedCopy
