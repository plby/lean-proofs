import ErdosProblems.Erdos593.TripleSystem.Expansion
import ErdosProblems.Erdos593.TripleSystem.ObligatoryIsolatedReduction
import ErdosProblems.Erdos593.Graph.CompleteBipartite
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite bipartite reduction for private-vertex expansions

This file formalizes the finite reduction in Corollary 3.3 of the manuscript.
Every finite two-colourable graph maps injectively and adjacency-preservingly
into a balanced finite complete bipartite graph.  Such a graph copy lifts to a
triple-system embedding of private-vertex expansions.  Consequently, the
obligatoriness of all finite `K_{n,n}^+` atoms implies the obligatoriness of
the expansion of every finite two-colourable graph.

The two finite parts are universe-lifted.  This is mathematically immaterial,
but it keeps the atom in the same vertex and edge universes as the source, as
required by the universe-indexed definition of `IsObligatory`.
-/

namespace Erdos593

universe u

namespace TripleSystem

/-- Backwards-compatible triple-system-layer name for the graph-level finite
part. -/
abbrev FiniteBipartitePart (n : ℕ) := Erdos593.FiniteBipartitePart.{u} n

/-- Backwards-compatible triple-system-layer name for the graph-level
balanced complete bipartite graph. -/
abbrev completeBipartiteNN (n : ℕ) := Erdos593.completeBipartiteNN.{u} n

namespace SimpleGraph

variable {V W : Type u}
variable (G : _root_.SimpleGraph V) (H : _root_.SimpleGraph W)

/-- A finite two-colouring gives an injective adjacency-preserving map into
the balanced complete bipartite graph whose two sides both have size `|V|`.
This is a non-induced graph copy, which is the notion needed for expansion
embeddings. -/
noncomputable def copyCompleteBipartiteNN [Fintype V]
    (C : G.Coloring (Fin 2)) :
    _root_.SimpleGraph.Copy G
      (completeBipartiteNN.{u} (Fintype.card V)) := by
  classical
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let vertexMap : V →
      FiniteBipartitePart.{u} (Fintype.card V) ⊕
        FiniteBipartitePart.{u} (Fintype.card V) := fun x ↦
    if C x = 0 then Sum.inl (ULift.up (e x))
    else Sum.inr (ULift.up (e x))
  have hinjective : Function.Injective vertexMap := by
    intro x y hxy
    have h := congrArg
      (Sum.elim (fun z ↦ z.down) (fun z ↦ z.down)) hxy
    have he : e x = e y := by
      simpa only [vertexMap, apply_ite, Sum.elim_inl, Sum.elim_inr,
        ULift.down_up, ite_self] using! h
    exact e.injective he
  refine
    { toHom :=
        { toFun := vertexMap
          map_rel' := ?_ }
      injective' := hinjective }
  intro x y hxy
  have hcolors : C x ≠ C y := C.valid hxy
  by_cases hx : C x = 0
  · have hy : C y ≠ 0 := by
      intro hy
      exact hcolors (hx.trans hy.symm)
    simp [vertexMap, hx, hy]
  · have hcx : C x = 1 := Fin.eq_one_of_ne_zero (C x) hx
    have hy : C y = 0 := by
      by_contra hy
      have hcy : C y = 1 := Fin.eq_one_of_ne_zero (C y) hy
      exact hcolors (hcx.trans hcy.symm)
    simp [vertexMap, hx, hy]

end SimpleGraph

variable {V W : Type u}
variable {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}

/-- An injective adjacency-preserving graph map lifts canonically to a
triple-system embedding of private-vertex expansions.  Core vertices use the
given vertex injection, while each private edge point is sent to the private
point of the image edge. -/
def privateVertexExpansionEmbeddingOfCopy
    (f : _root_.SimpleGraph.Copy G H) :
    (privateVertexExpansion G).Embedding (privateVertexExpansion H) where
  vertex := Function.Embedding.sumMap f.toEmbedding f.mapEdgeSet
  edge := f.mapEdgeSet
  map_edge := by
    intro e
    rcases e with ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | _ x y =>
        change
          f.toEmbedding.sumMap f.mapEdgeSet ''
              {p | PrivateVertexExpansion.Inc G p ⟨s(x, y), he⟩} =
            {p | PrivateVertexExpansion.Inc H p
              (f.mapEdgeSet ⟨s(x, y), he⟩)}
        rw [PrivateVertexExpansion.incidenceSet_eq G he]
        ext p
        rcases p with p | p
        · simp [Function.Embedding.sumMap, PrivateVertexExpansion.core,
            PrivateVertexExpansion.Inc,
            PrivateVertexExpansion.privateVertex,
            _root_.SimpleGraph.Copy.mapEdgeSet,
            _root_.SimpleGraph.Hom.mapEdgeSet]
          constructor
          · rintro (h | h)
            · exact Or.inl h.symm
            · exact Or.inr h.symm
          · rintro (h | h)
            · exact Or.inl h.symm
            · exact Or.inr h.symm
        · simp [Function.Embedding.sumMap, PrivateVertexExpansion.core,
            PrivateVertexExpansion.Inc,
            PrivateVertexExpansion.privateVertex,
            _root_.SimpleGraph.Copy.mapEdgeSet,
            _root_.SimpleGraph.Hom.mapEdgeSet]
          constructor <;> intro h <;> exact h.symm

/-- The isolated reduction of a finite two-colourable graph expansion embeds
in the corresponding balanced complete-bipartite expansion.  Passing through
the isolated reduction makes explicit that isolated graph vertices play no
role in the edge pattern. -/
noncomputable def isolatedExpansionEmbeddingCompleteBipartiteNN
    [Fintype V] (C : G.Coloring (Fin 2)) :
    (privateVertexExpansion G).isolatedReduction.Embedding
      (privateVertexExpansion
        (completeBipartiteNN.{u} (Fintype.card V))) :=
  (isolatedReductionEmbedding (privateVertexExpansion G)).trans
    (privateVertexExpansionEmbeddingOfCopy
      (SimpleGraph.copyCompleteBipartiteNN G C))

/-- **Finite bipartite reduction (manuscript Corollary 3.3).**

If every finite balanced complete-bipartite expansion `K_{n,n}^+` is
obligatory, then the private-vertex expansion of every finite two-colourable
graph is obligatory.  This theorem contains only the finite reduction; it
does not assert the infinitary theorem that the atoms themselves are
obligatory. -/
theorem privateVertexExpansion_isObligatory_of_completeBipartiteNN
    [Fintype V] (hG : G.Colorable 2)
    (hAtoms : ∀ n : ℕ,
      (privateVertexExpansion (completeBipartiteNN.{u} n)).IsObligatory) :
    (privateVertexExpansion G).IsObligatory := by
  classical
  obtain ⟨C⟩ := hG
  apply IsObligatory.of_isolatedReduction
  exact (hAtoms (Fintype.card V)).of_sourceEmbedding
    (isolatedExpansionEmbeddingCompleteBipartiteNN C)

end TripleSystem

end Erdos593
