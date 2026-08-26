import ErdosProblems.Erdos593.TripleSystem.Basic

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Disjoint unions of triple systems

This file defines the binary disjoint union of two edge-indexed triple systems.
Both vertices and edge indices are tagged by a sum, so incidences occur exactly
within the corresponding summand.
-/

namespace Erdos593

universe u v w z

namespace TripleSystem

variable {V : Type u} {E : Type v} {W : Type w} {D : Type z}

/-- Incidence in a disjoint union: an incident vertex and edge must lie in the
same summand, where incidence is inherited from that summand. -/
def disjointUnionInc (F : TripleSystem V E) (G : TripleSystem W D) :
    V ⊕ W → E ⊕ D → Prop
  | .inl x, .inl e => F.Inc x e
  | .inr y, .inr d => G.Inc y d
  | .inl _, .inr _ => False
  | .inr _, .inl _ => False

/-- The binary disjoint union of two simple triple systems. -/
def disjointUnion (F : TripleSystem V E) (G : TripleSystem W D) :
    TripleSystem (V ⊕ W) (E ⊕ D) where
  Inc := disjointUnionInc F G
  edge_ncard := by
    rintro (e | d)
    · have hset :
          {x : V ⊕ W | disjointUnionInc F G x (.inl e)} =
            Sum.inl '' F.edgeSet e := by
        ext x
        cases x <;> simp [disjointUnionInc, edgeSet]
      rw [hset, Set.ncard_image_of_injective _ Sum.inl_injective,
        F.edgeSet_ncard]
    · have hset :
          {x : V ⊕ W | disjointUnionInc F G x (.inr d)} =
            Sum.inr '' G.edgeSet d := by
        ext x
        cases x <;> simp [disjointUnionInc, edgeSet]
      rw [hset, Set.ncard_image_of_injective _ Sum.inr_injective,
        G.edgeSet_ncard]
  simple := by
    intro a b hab
    cases a with
    | inl e =>
        cases b with
        | inl f =>
            apply congrArg Sum.inl
            apply F.simple
            ext x
            have hx := Set.ext_iff.mp hab (Sum.inl x)
            simpa [disjointUnionInc] using! hx
        | inr d =>
            exfalso
            have hne : Set.ncard {x : V | F.Inc x e} ≠ 0 := by
              rw [F.edge_ncard e]
              decide
            obtain ⟨x, hx⟩ := Set.nonempty_of_ncard_ne_zero hne
            have hmem := (Set.ext_iff.mp hab (Sum.inl x)).mp hx
            simp [disjointUnionInc] at hmem
    | inr d =>
        cases b with
        | inl e =>
            exfalso
            have hne : Set.ncard {y : W | G.Inc y d} ≠ 0 := by
              rw [G.edge_ncard d]
              decide
            obtain ⟨y, hy⟩ := Set.nonempty_of_ncard_ne_zero hne
            have hmem := (Set.ext_iff.mp hab (Sum.inr y)).mp hy
            simp [disjointUnionInc] at hmem
        | inr c =>
            apply congrArg Sum.inr
            apply G.simple
            ext y
            have hy := Set.ext_iff.mp hab (Sum.inr y)
            simpa [disjointUnionInc] using! hy

@[simp]
theorem disjointUnion_inc_inl_inl (F : TripleSystem V E) (G : TripleSystem W D)
    (x : V) (e : E) :
    (F.disjointUnion G).Inc (.inl x) (.inl e) ↔ F.Inc x e :=
  Iff.rfl

@[simp]
theorem disjointUnion_inc_inr_inr (F : TripleSystem V E) (G : TripleSystem W D)
    (y : W) (d : D) :
    (F.disjointUnion G).Inc (.inr y) (.inr d) ↔ G.Inc y d :=
  Iff.rfl

@[simp]
theorem disjointUnion_not_inc_inl_inr (F : TripleSystem V E) (G : TripleSystem W D)
    (x : V) (d : D) :
    ¬(F.disjointUnion G).Inc (.inl x) (.inr d) := by
  simp [disjointUnion, disjointUnionInc]

@[simp]
theorem disjointUnion_not_inc_inr_inl (F : TripleSystem V E) (G : TripleSystem W D)
    (y : W) (e : E) :
    ¬(F.disjointUnion G).Inc (.inr y) (.inl e) := by
  simp [disjointUnion, disjointUnionInc]

@[simp]
theorem disjointUnion_edgeSet_inl (F : TripleSystem V E) (G : TripleSystem W D)
    (e : E) :
    (F.disjointUnion G).edgeSet (.inl e) = Sum.inl '' F.edgeSet e := by
  ext x
  cases x <;> simp [edgeSet, disjointUnion, disjointUnionInc]

@[simp]
theorem disjointUnion_edgeSet_inr (F : TripleSystem V E) (G : TripleSystem W D)
    (d : D) :
    (F.disjointUnion G).edgeSet (.inr d) = Sum.inr '' G.edgeSet d := by
  ext x
  cases x <;> simp [edgeSet, disjointUnion, disjointUnionInc]

end TripleSystem

end Erdos593
