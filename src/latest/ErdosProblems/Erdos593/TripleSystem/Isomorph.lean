import ErdosProblems.Erdos593.TripleSystem.Basic

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Triple-system isomorphisms

An isomorphism of edge-indexed triple systems relabels both the vertices and
the edge indices by equivalences, and preserves incidence in both directions.
Relabelling only the vertices would not be sufficient: the edge indices are
part of the representation used by the Levi graph.
-/

namespace Erdos593

universe u v u' v' u'' v''

namespace TripleSystem

variable {V : Type u} {E : Type v}
variable {V' : Type u'} {E' : Type v'}
variable {V'' : Type u''} {E'' : Type v''}

/-- An incidence-preserving relabelling of both vertices and edge indices. -/
structure Iso (F : TripleSystem V E) (F' : TripleSystem V' E') where
  /-- The bijective relabelling of vertices. -/
  vertexEquiv : V ≃ V'
  /-- The bijective relabelling of edge indices. -/
  edgeEquiv : E ≃ E'
  /-- Incidence is preserved and reflected by the two relabellings. -/
  map_inc_iff : ∀ x e,
    F.Inc x e ↔ F'.Inc (vertexEquiv x) (edgeEquiv e)

namespace Iso

variable {F : TripleSystem V E}
variable {F' : TripleSystem V' E'}
variable {F'' : TripleSystem V'' E''}

/-- The identity relabelling. -/
def refl (F : TripleSystem V E) : Iso F F where
  vertexEquiv := Equiv.refl V
  edgeEquiv := Equiv.refl E
  map_inc_iff := fun _ _ => Iff.rfl

/-- Reverse an isomorphism by using the inverse vertex and edge relabellings. -/
def symm (f : Iso F F') : Iso F' F where
  vertexEquiv := f.vertexEquiv.symm
  edgeEquiv := f.edgeEquiv.symm
  map_inc_iff := by
    intro x e
    simpa using!
      (f.map_inc_iff (f.vertexEquiv.symm x) (f.edgeEquiv.symm e)).symm

/-- Compose two incidence-preserving relabellings. -/
def trans (f : Iso F F') (g : Iso F' F'') : Iso F F'' where
  vertexEquiv := f.vertexEquiv.trans g.vertexEquiv
  edgeEquiv := f.edgeEquiv.trans g.edgeEquiv
  map_inc_iff := by
    intro x e
    exact (f.map_inc_iff x e).trans
      (g.map_inc_iff (f.vertexEquiv x) (f.edgeEquiv e))

end Iso

/-- Two edge-indexed triple systems are isomorphic when some simultaneous
vertex-and-edge relabelling preserves incidence. -/
def Isomorphic (F : TripleSystem V E) (F' : TripleSystem V' E') : Prop :=
  Nonempty (Iso F F')

/-- Every triple system is isomorphic to itself. -/
@[refl]
theorem isomorphic_refl (F : TripleSystem V E) : Isomorphic F F :=
  ⟨Iso.refl F⟩

/-- Triple-system isomorphism is symmetric. -/
theorem Isomorphic.symm {F : TripleSystem V E} {F' : TripleSystem V' E'}
    (h : Isomorphic F F') : Isomorphic F' F :=
  h.map Iso.symm

/-- Triple-system isomorphism is transitive, including across different
vertex and edge-index types. -/
theorem Isomorphic.trans
    {F : TripleSystem V E} {F' : TripleSystem V' E'}
    {F'' : TripleSystem V'' E''}
    (h : Isomorphic F F') (h' : Isomorphic F' F'') : Isomorphic F F'' := by
  rcases h with ⟨f⟩
  rcases h' with ⟨g⟩
  exact ⟨f.trans g⟩

/-- Reversing both sides does not change whether two systems are isomorphic. -/
theorem isomorphic_comm {F : TripleSystem V E} {F' : TripleSystem V' E'} :
    Isomorphic F F' ↔ Isomorphic F' F :=
  ⟨Isomorphic.symm, Isomorphic.symm⟩

/-- On systems with fixed vertex and edge-index types, isomorphism is an
equivalence relation. -/
theorem isomorphic_equivalence :
    Equivalence (@Isomorphic V E V E) :=
  ⟨isomorphic_refl, Isomorphic.symm, Isomorphic.trans⟩

/-- The setoid of triple systems modulo simultaneous vertex-and-edge
relabelling.  This is intentionally a named definition rather than a global
instance. -/
def isomorphicSetoid : Setoid (TripleSystem V E) where
  r := Isomorphic
  iseqv := isomorphic_equivalence

end TripleSystem

end Erdos593
