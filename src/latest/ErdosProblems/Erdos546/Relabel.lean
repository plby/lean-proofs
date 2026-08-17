/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos546.Basic

/-!
# Erdős Problem 546: relabeling finite reservoirs

The sparsification input used later is stated for graphs on `Fin n`.  This file
transports its output through `SimpleGraph.overFinIso` and through the induced
subgraph embedding of a reservoir into the ambient colour graph.  In
particular, the complement case is transported by `Embedding.complEquiv`, so
the two colours are treated correctly.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos546

open Finset
open SimpleGraph

/-! ## Monochromatic pairs and graph embeddings -/

/-- A monochromatic pair maps along an induced graph embedding.  The use of a
graph embedding, rather than a mere graph homomorphism, is essential in the
complementary colour. -/
theorem MonoPair.map_embedding {V W : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W} {X Z : Finset V}
    (h : MonoPair G X Z) (f : G ↪g H) :
    MonoPair H (X.map f.toEmbedding) (Z.map f.toEmbedding) := by
  classical
  refine ⟨(Finset.disjoint_map f.toEmbedding).2 h.1, ?_, ?_⟩
  · intro _ hx _ hz hne
    rw [Finset.coe_map] at hx hz
    rcases hx with ⟨x, hx, rfl⟩
    rcases hz with ⟨z, hz, rfl⟩
    exact f.toHom.map_rel' (h.2.1 hx hz fun hxz ↦ hne (congrArg f hxz))
  · intro _ hx _ hz
    rw [Finset.mem_map] at hx hz
    rcases hx with ⟨x, hx, rfl⟩
    rcases hz with ⟨z, hz, rfl⟩
    exact f.toHom.map_rel' (h.2.2 x hx z hz)

/-- `HasMonoPair` is preserved by induced graph embeddings, in either colour.
For the complementary colour this uses the corresponding embedding of graph
complements. -/
theorem HasMonoPair.map_embedding {V W : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W} {X Z : Finset V}
    (h : HasMonoPair G X Z) (f : G ↪g H) :
    HasMonoPair H (X.map f.toEmbedding) (Z.map f.toEmbedding) := by
  rcases h with h | h
  · exact Or.inl (h.map_embedding f)
  · exact Or.inr (h.map_embedding
      ((SimpleGraph.Embedding.complEquiv (G := G) (H := H)).toFun f))

/-! ## `overFin` bridges -/

/-- Relabeling a finite host graph by `Fin` does not change which arbitrary
target graphs it contains. -/
theorem isContained_overFin_iff {U V : Type*} [Fintype V]
    (F : SimpleGraph U) (G : SimpleGraph V) :
    F ⊑ G.overFin rfl ↔ F ⊑ G := by
  exact isContained_congr Iso.refl (G.overFinIso rfl).symm

/-- Relabeling a finite graph by `Fin` preserves its maximum degree exactly. -/
theorem maxDegree_overFin_eq {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (G.overFin rfl).Adj] :
    (G.overFin rfl).maxDegree = G.maxDegree := by
  exact (G.overFinIso rfl).maxDegree_eq.symm

/-- Restricting to `Y` and relabeling by `Fin Y.card` preserves exactly the
number of ordered edges inside the reservoir. -/
theorem squareEdgeCount_induce_overFin_univ_eq
    {N : ℕ} (R : SimpleGraph (Fin N)) (Y : Finset (Fin N)) :
    squareEdgeCount
        ((R.induce (↑Y : Set (Fin N))).overFin (Fintype.card_coe Y)) Finset.univ =
      squareEdgeCount R Y := by
  classical
  let I : SimpleGraph (↑Y : Set (Fin N)) := R.induce (↑Y : Set (Fin N))
  let J : SimpleGraph (Fin Y.card) := I.overFin (Fintype.card_coe Y)
  let e : I ≃g J := I.overFinIso (Fintype.card_coe Y)
  unfold squareEdgeCount
  apply Finset.card_bij
      (fun p _ ↦ ((e.symm p.1).1, (e.symm p.2).1))
  · intro p hp
    have hp' := J.mem_interedges_iff.mp hp
    apply R.mem_interedges_iff.mpr
    refine ⟨(e.symm p.1).2, (e.symm p.2).2, ?_⟩
    exact e.symm.toHom.map_rel' hp'.2.2
  · intro p hp r hr hpr
    apply Prod.ext
    · apply e.symm.injective
      apply Subtype.ext
      exact congrArg Prod.fst hpr
    · apply e.symm.injective
      apply Subtype.ext
      exact congrArg Prod.snd hpr
  · intro p hp
    have hp' := R.mem_interedges_iff.mp hp
    let x : Fin Y.card := e ⟨p.1, hp'.1⟩
    let y : Fin Y.card := e ⟨p.2, hp'.2.1⟩
    refine ⟨(x, y), ?_, ?_⟩
    · apply J.mem_interedges_iff.mpr
      refine ⟨Finset.mem_univ _, Finset.mem_univ _, ?_⟩
      exact e.toHom.map_rel' hp'.2.2
    · simp [x, y, e]

/-- A square-sparse reservoir remains square-sparse after restricting to it
and relabeling its induced graph by `Fin Y.card`. -/
theorem squareSparse_induce_overFin_univ
    {N q : ℕ} (R : SimpleGraph (Fin N)) (Y : Finset (Fin N))
    (h : SquareSparse q R Y) :
    SquareSparse q ((R.induce (↑Y : Set (Fin N))).overFin (Fintype.card_coe Y))
      Finset.univ := by
  classical
  unfold SquareSparse at h ⊢
  rw [squareEdgeCount_induce_overFin_univ_eq R Y]
  simpa using h

/-- A copy in the `Fin`-relabeling of an induced reservoir is a copy in the
ambient graph. -/
theorem isContained_of_isContained_overFin_induce
    {U : Type*} {N : ℕ} (F : SimpleGraph U) (R : SimpleGraph (Fin N))
    (Y : Finset (Fin N))
    (h : F ⊑ (R.induce (↑Y : Set (Fin N))).overFin rfl) :
    F ⊑ R := by
  exact ((isContained_overFin_iff F (R.induce (↑Y : Set (Fin N)))).mp h).trans
    ⟨Copy.induce R (↑Y : Set (Fin N))⟩

/-! ## Relabeling a reservoir pair back to the ambient graph -/

/-- Transport a monochromatic pair found after relabeling the induced graph on
`Y` by `Fin Y.card` back to the ambient graph.  Both cardinalities are
preserved exactly. -/
theorem hasMonoPair_overFin_induce_to_ambient
    {N : ℕ} (R : SimpleGraph (Fin N)) (Y : Finset (Fin N))
    (X Z : Finset (Fin Y.card))
    (h : HasMonoPair ((R.induce (↑Y : Set (Fin N))).overFin
      (Fintype.card_coe Y)) X Z) :
    ∃ X' Z' : Finset (Fin N), HasMonoPair R X' Z' ∧
      X'.card = X.card ∧ Z'.card = Z.card := by
  classical
  let I : SimpleGraph (↑Y : Set (Fin N)) := R.induce (↑Y : Set (Fin N))
  let e : I ≃g I.overFin (Fintype.card_coe Y) :=
    I.overFinIso (Fintype.card_coe Y)
  let f : I.overFin (Fintype.card_coe Y) ↪g R := (SimpleGraph.Embedding.induce
    (↑Y : Set (Fin N))).comp e.symm.toEmbedding
  refine ⟨X.map f.toEmbedding, Z.map f.toEmbedding, h.map_embedding f, ?_, ?_⟩
  · exact Finset.card_map _
  · exact Finset.card_map _

end Erdos546
