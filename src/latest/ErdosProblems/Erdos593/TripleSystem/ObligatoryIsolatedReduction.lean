import ErdosProblems.Erdos593.TripleSystem.Isolated
import ErdosProblems.Erdos593.TripleSystem.ObligatoryDisjointUnion
import Mathlib.Data.Countable.Basic

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Isolated vertices do not affect obligatoriness

Deleting isolated vertices preserves all source edges.  The easy implication is
therefore just downward closure of appearance under a source embedding.  For
the converse, an embedding of the isolated reduction into an infinite host is
extended by sending the finitely many isolated vertices injectively into the
complement of its finite vertex image.  Since our embeddings are non-induced,
no condition on host edges involving these new vertices is required.
-/

namespace Erdos593

open scoped Cardinal

universe u v

namespace TripleSystem

variable {V W X : Type u} {E D A : Type v}
variable {F : TripleSystem V E} {G : TripleSystem X A}
variable {H : TripleSystem W D}

/-- The canonical embedding of the isolated-point reduction into the original
triple system. -/
def isolatedReductionEmbedding (F : TripleSystem V E) :
    F.isolatedReduction.Embedding F where
  vertex := ⟨Subtype.val, Subtype.val_injective⟩
  edge := id
  map_edge := by
    intro e
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, F.not_isolated_of_inc hx⟩, hx, rfl⟩

/-- Appearance is downward closed under embeddings of the source. -/
theorem Appears.of_sourceEmbedding (i : G.Embedding F) (hF : F.Appears H) :
    G.Appears H := by
  rcases hF with ⟨f⟩
  exact ⟨i.trans f⟩

/-- Obligatory systems are downward closed under embeddings of the source. -/
theorem IsObligatory.of_sourceEmbedding (i : G.Embedding F)
    (hF : F.IsObligatory) : G.IsObligatory := by
  intro Y B _ K hK
  exact (hF Y B K hK).of_sourceEmbedding i

/-- Deleting isolated vertices preserves obligatoriness in the easy
direction, with no finiteness assumption. -/
theorem IsObligatory.isolatedReduction (hF : F.IsObligatory) :
    F.isolatedReduction.IsObligatory :=
  hF.of_sourceEmbedding (isolatedReductionEmbedding F)

/-- The identity vertex map is a proper colouring. -/
theorem identity_isProperColoring (H : TripleSystem W D) :
    H.IsProperColoring id := by
  intro e
  have hne : (H.edgeSet e).ncard ≠ 0 := by
    rw [H.edgeSet_ncard]
    decide
  obtain ⟨x, hx⟩ := Set.nonempty_of_ncard_ne_zero hne
  obtain ⟨y, hy, hyx⟩ := H.exists_other_incident e hx
  exact ⟨x, hx, y, hy, hyx.symm⟩

/-- The chromatic cardinal is bounded by the cardinality of the vertex type. -/
theorem chromaticCardinal_le_mk_vertices (H : TripleSystem W D) :
    H.chromaticCardinal ≤ #W :=
  (H.chromaticCardinal_le_mk_iff).2 ⟨id, H.identity_isProperColoring⟩

/-- An embedding of the isolated reduction of a finite triple system into an
infinite host extends to the whole source.  The new isolated vertices are sent
injectively into the complement of the old (finite) image. -/
noncomputable def Embedding.extendIsolatedReduction [Fintype V] [Infinite W]
    (f : F.isolatedReduction.Embedding H) : F.Embedding H := by
  classical
  let R : Set W := Set.range f.vertex
  have hR : R.Finite := Set.finite_range f.vertex
  letI : Infinite (Rᶜ : Set W) := hR.infinite_compl.to_subtype
  let toNat : {x : V // F.IsIsolated x} ↪ ℕ :=
    Classical.choice (nonempty_embedding_nat {x : V // F.IsIsolated x})
  let unused : {x : V // F.IsIsolated x} ↪ (Rᶜ : Set W) :=
    toNat.trans (Infinite.natEmbedding (Rᶜ : Set W))
  let vertexMap : V → W := fun x ↦
    if hx : F.IsIsolated x then (unused ⟨x, hx⟩ : W)
    else f.vertex ⟨x, hx⟩
  have vertexMap_injective : Function.Injective vertexMap := by
    intro x y hxy
    by_cases hx : F.IsIsolated x
    · by_cases hy : F.IsIsolated y
      · have hu : unused ⟨x, hx⟩ = unused ⟨y, hy⟩ := by
          apply Subtype.ext
          simpa [vertexMap, hx, hy] using! hxy
        exact congrArg Subtype.val (unused.injective hu)
      · have hbad : (unused ⟨x, hx⟩ : W) ∈ R := by
          refine ⟨⟨y, hy⟩, ?_⟩
          simpa [vertexMap, hx, hy] using! hxy.symm
        exact False.elim ((unused ⟨x, hx⟩).property hbad)
    · by_cases hy : F.IsIsolated y
      · have hbad : (unused ⟨y, hy⟩ : W) ∈ R := by
          refine ⟨⟨x, hx⟩, ?_⟩
          simpa [vertexMap, hx, hy] using! hxy
        exact False.elim ((unused ⟨y, hy⟩).property hbad)
      · have hf : f.vertex ⟨x, hx⟩ = f.vertex ⟨y, hy⟩ := by
          simpa [vertexMap, hx, hy] using! hxy
        exact congrArg Subtype.val (f.vertex.injective hf)
  refine
    { vertex := ⟨vertexMap, vertexMap_injective⟩
      edge := f.edge
      map_edge := ?_ }
  intro e
  calc
    vertexMap '' F.edgeSet e =
        f.vertex '' F.isolatedReduction.edgeSet e := by
      ext w
      constructor
      · rintro ⟨x, hxe, rfl⟩
        have hx : ¬F.IsIsolated x := F.not_isolated_of_inc hxe
        refine ⟨⟨x, hx⟩, hxe, ?_⟩
        simp [vertexMap, hx]
      · rintro ⟨x, hxe, rfl⟩
        refine ⟨x.1, hxe, ?_⟩
        simp [vertexMap, x.2]
    _ = H.edgeSet (f.edge e) := f.map_edge e

/-- The hard direction: if the isolated reduction of a finite triple system is
obligatory, then so is the original system. -/
theorem IsObligatory.of_isolatedReduction [Fintype V]
    (hF : F.isolatedReduction.IsObligatory) : F.IsObligatory := by
  intro Y B _ K hK
  obtain ⟨f⟩ := hF Y B K hK
  have hvertices : ℵ₀ ≤ #Y :=
    hK.le.trans K.chromaticCardinal_le_mk_vertices
  letI : Infinite Y := Cardinal.aleph0_le_mk_iff.mp hvertices
  exact ⟨f.extendIsolatedReduction⟩

/-- For a finite triple system, deleting isolated vertices preserves and
reflects obligatoriness. -/
theorem isObligatory_iff_isolatedReduction [Fintype V] :
    F.IsObligatory ↔ F.isolatedReduction.IsObligatory := by
  constructor
  · exact IsObligatory.isolatedReduction
  · exact IsObligatory.of_isolatedReduction

end TripleSystem

end Erdos593
