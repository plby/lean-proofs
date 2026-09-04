import ErdosProblems.Erdos593.TripleSystem.Constructive
import ErdosProblems.Erdos593.TripleSystem.EdgeRestriction
import ErdosProblems.Erdos593.TripleSystem.SingleEdgePiece
import Mathlib.Combinatorics.SimpleGraph.Finite

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Constructibility of canonical one-edge pieces

An isolated hyperedge-node left by deleting all Levi bridges contributes one
triple, even though it contributes no edge to the contracted ordinary graph.
This file identifies that triple with the private-vertex expansion of the
canonical graph `K₂`, and identifies it with the exact one-edge restriction
of the ambient triple system.
-/

namespace Erdos593

open scoped Sym2

universe u w

namespace TripleSystem

/-- A universe-polymorphic two-element vertex type. -/
abbrev OneEdgeVertex : Type w := ULift.{w} (Fin 2)

/-- The canonical graph `K₂`, used to generate a single triple. -/
abbrev oneEdgeGraph : _root_.SimpleGraph (OneEdgeVertex.{w}) :=
  _root_.SimpleGraph.completeGraph OneEdgeVertex

/-- The unique edge of `oneEdgeGraph`. -/
def oneEdgeGraphEdge : oneEdgeGraph.{w}.edgeSet :=
  ⟨s(ULift.up 0, ULift.up 1), by simp [oneEdgeGraph]⟩

/-- Every edge of `oneEdgeGraph` is its displayed edge. -/
theorem oneEdgeGraph_edge_eq (a : oneEdgeGraph.{w}.edgeSet) :
    a = oneEdgeGraphEdge.{w} := by
  apply Subtype.ext
  rcases a with ⟨a, ha⟩
  induction a using Sym2.inductionOn with
  | _ x y =>
      change x ≠ y at ha
      rcases x with ⟨x⟩
      rcases y with ⟨y⟩
      fin_cases x <;> fin_cases y
      · exact (ha rfl).elim
      · rfl
      · simp [oneEdgeGraphEdge]
      · exact (ha rfl).elim

/-- Every point of the expansion of `K₂` is incident with its unique
expanded edge. -/
theorem oneEdgeExpansion_inc
    (p : PrivateVertexExpansion.Point oneEdgeGraph.{w})
    (a : PrivateVertexExpansion.Edge oneEdgeGraph.{w}) :
    (privateVertexExpansion oneEdgeGraph.{w}).Inc p a := by
  have ha : a = oneEdgeGraphEdge.{w} := oneEdgeGraph_edge_eq a
  subst a
  rcases p with x | b
  · change x ∈ (s(ULift.up 0, ULift.up 1) : Sym2 OneEdgeVertex)
    rcases x with ⟨x⟩
    fin_cases x <;> simp
  · change b = oneEdgeGraphEdge.{w}
    exact oneEdgeGraph_edge_eq b

/-- The canonical two-colouring of `K₂`. -/
theorem oneEdgeGraph_colorable_two : oneEdgeGraph.{w}.Colorable 2 := by
  refine ⟨_root_.SimpleGraph.Coloring.mk (fun x => x.down) ?_⟩
  intro x y hxy h
  apply hxy
  apply ULift.ext
  exact h

/-- The expansion of `K₂` has three points. -/
theorem oneEdgeExpansion_vertex_card :
    Fintype.card (PrivateVertexExpansion.Point oneEdgeGraph.{w}) = 3 := by
  have hedge : Fintype.card oneEdgeGraph.{w}.edgeSet = 1 := by
    let : Unique oneEdgeGraph.{w}.edgeSet :=
      { default := oneEdgeGraphEdge.{w}
        uniq := oneEdgeGraph_edge_eq }
    exact Fintype.card_unique
  simp only [PrivateVertexExpansion.Point, PrivateVertexExpansion.CoreVertex,
    PrivateVertexExpansion.PrivateVertex, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_ulift, hedge]

/-- The expansion of `K₂` has one edge. -/
theorem oneEdgeExpansion_edge_card :
    Fintype.card (PrivateVertexExpansion.Edge oneEdgeGraph.{w}) = 1 := by
  let : Unique oneEdgeGraph.{w}.edgeSet :=
    { default := oneEdgeGraphEdge.{w}
      uniq := oneEdgeGraph_edge_eq }
  exact Fintype.card_unique

noncomputable section

variable {V : Type u} {E : Type u} (F : TripleSystem V E)

/-- An arbitrary bijection is incidence-preserving here because both systems
have one edge and every point lies on it. -/
noncomputable def oneEdgeExpansionSingleEdgePieceIso [Fintype V] (e : E) :
    Iso (privateVertexExpansion oneEdgeGraph.{u}) (F.singleEdgePiece e) := by
  letI : Fintype (F.edgeSet e) := Fintype.ofFinite _
  exact
    { vertexEquiv := Fintype.equivOfCardEq (by
        rw [oneEdgeExpansion_vertex_card, Set.fintypeCard_eq_ncard]
        exact (F.edge_ncard e).symm)
      edgeEquiv := Fintype.equivOfCardEq (by
        rw [oneEdgeExpansion_edge_card]
        simp [SingleEdgeIndex])
      map_inc_iff := by
        intro p a
        constructor
        · intro _
          trivial
        · intro _
          exact oneEdgeExpansion_inc p a }

/-- Every canonical one-edge piece belongs to the constructive class. -/
theorem singleEdgePiece_constructible [Fintype V] (e : E) :
    Constructible (F.singleEdgePiece e) := by
  have hExpansion : Constructible
      (privateVertexExpansion oneEdgeGraph.{u}) :=
    Constructible.ofExpansion oneEdgeGraph.{u} oneEdgeGraph_colorable_two
  exact Constructible.ofIso hExpansion
    (oneEdgeExpansionSingleEdgePieceIso F e)

/-- The points on the selected edge are exactly the support of the singleton
edge-index set. -/
def singleEdgePieceRestrictionVertexEquiv (e : E) :
    F.edgeSet e ≃ F.EdgeSupport ({e} : Set E) where
  toFun x := ⟨x.1, e, Set.mem_singleton e, x.2⟩
  invFun x := ⟨x.1, by
    rcases x.2 with ⟨f, hf, hxf⟩
    have hfe : f = e := Set.mem_singleton_iff.mp hf
    subst f
    exact hxf⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

/-- The unique edge index of a one-edge piece corresponds to the selected
ambient edge. -/
def singleEdgePieceRestrictionEdgeEquiv (e : E) :
    SingleEdgeIndex.{u} ≃ ({e} : Set E) where
  toFun _ := ⟨e, Set.mem_singleton e⟩
  invFun _ := ULift.up ()
  left_inv x := Subsingleton.elim _ _
  right_inv x := by
    apply Subtype.ext
    exact (Set.mem_singleton_iff.mp x.2).symm

/-- The canonical one-edge piece is exactly the ambient restriction to that
single edge. -/
def singleEdgePieceRestrictionIso (e : E) :
    Iso (F.singleEdgePiece e) (F.edgeRestriction ({e} : Set E)) where
  vertexEquiv := singleEdgePieceRestrictionVertexEquiv F e
  edgeEquiv := singleEdgePieceRestrictionEdgeEquiv e
  map_inc_iff := by
    intro x d
    constructor
    · intro _
      exact x.2
    · intro _
      trivial

/-- Every exact singleton-edge restriction belongs to the constructive
class. -/
theorem singletonEdgeRestriction_constructible [Fintype V] (e : E) :
    Constructible (F.edgeRestriction ({e} : Set E)) :=
  Constructible.ofIso (singleEdgePiece_constructible F e)
    (singleEdgePieceRestrictionIso F e)

end

end TripleSystem
end Erdos593
