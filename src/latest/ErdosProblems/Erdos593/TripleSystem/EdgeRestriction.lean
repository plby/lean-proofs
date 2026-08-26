import ErdosProblems.Erdos593.TripleSystem.Embedding

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Edge restrictions

For reconstruction, a set of source hyperedges determines an exact subsystem
on the union of their incident vertices.  The canonical embedding records this
subsystem as a non-induced copy in the ambient triple system.
-/

namespace Erdos593

universe u v

namespace TripleSystem

variable {V : Type u} {E : Type v} (F : TripleSystem V E)

/-- The set of points lying on at least one edge whose index belongs to `S`. -/
def edgeSupportSet (S : Set E) : Set V :=
  {x | ∃ e : E, e ∈ S ∧ F.Inc x e}

/-- The point support of a finite family of triple edges is finite. -/
theorem edgeSupportSet_finite {S : Set E} (hS : S.Finite) :
    (F.edgeSupportSet S).Finite := by
  induction S, hS using Set.Finite.induction_on with
  | empty =>
      simp [edgeSupportSet]
  | insert hnotmem hfinite ih =>
      rename_i e S
      rw [show F.edgeSupportSet (insert e S) =
        {x : V | F.Inc x e} ∪ F.edgeSupportSet S by
          ext x
          simp [edgeSupportSet]]
      exact (Set.finite_of_ncard_ne_zero (by
        rw [F.edge_ncard e]
        decide)).union ih

/-- The type of points supported by an edge-index set. -/
abbrev EdgeSupport (S : Set E) := F.edgeSupportSet S

/-- Restrict to the edges indexed by `S`, retaining exactly their incident
points. -/
def edgeRestriction (S : Set E) : TripleSystem (F.EdgeSupport S) S where
  Inc x e := F.Inc x.1 e.1
  edge_ncard := by
    intro e
    change Set.ncard {x : F.EdgeSupport S |
      (x : V) ∈ {y : V | F.Inc y e.1}} = 3
    rw [Set.ncard_subtype]
    have hsubset : {x : V | F.Inc x e.1} ⊆
        F.edgeSupportSet S := by
      intro x hx
      exact ⟨e.1, e.2, hx⟩
    change Set.ncard ({x : V | F.Inc x e.1} ∩ F.edgeSupportSet S) = 3
    rw [Set.inter_eq_left.mpr hsubset]
    exact F.edge_ncard e.1
  simple := by
    intro e d h
    apply Subtype.ext
    apply F.simple
    ext x
    constructor
    · intro hxe
      let x' : F.EdgeSupport S := ⟨x, e.1, e.2, hxe⟩
      have hx := Set.ext_iff.mp h x'
      exact hx.mp hxe
    · intro hxd
      let x' : F.EdgeSupport S := ⟨x, d.1, d.2, hxd⟩
      have hx := Set.ext_iff.mp h x'
      exact hx.mpr hxd

@[simp]
theorem edgeRestriction_inc (S : Set E) (x : F.EdgeSupport S) (e : S) :
    (F.edgeRestriction S).Inc x e ↔ F.Inc x.1 e.1 :=
  Iff.rfl

/-- The canonical embedding of an edge restriction into the ambient system. -/
def edgeRestrictionEmbedding (S : Set E) :
    (F.edgeRestriction S).Embedding F where
  vertex := ⟨Subtype.val, Subtype.val_injective⟩
  edge := Subtype.val
  map_edge := by
    intro e
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, e.1, e.2, hx⟩, hx, rfl⟩

end TripleSystem
end Erdos593
