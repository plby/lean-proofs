import ErdosProblems.Erdos593.TripleSystem.EdgeRestriction
import ErdosProblems.Erdos593.TripleSystem.Isolated
import ErdosProblems.Erdos593.TripleSystem.Isomorph

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The full edge restriction

If every vertex is incident with an edge, restricting to the full edge-index
set changes only the representation: its supported-vertex and edge subtypes are
canonically equivalent to the original types.
-/

namespace Erdos593

universe u v

namespace TripleSystem

variable {V : Type u} {E : Type v} (F : TripleSystem V E)

/-- Under the no-isolated-points hypothesis, every vertex belongs to the
support of the full edge-index set. -/
theorem mem_edgeSupportSet_univ (hF : F.HasNoIsolatedPoints) (x : V) :
    x ∈ F.edgeSupportSet Set.univ := by
  rcases F.not_isolated_iff_exists_inc.mp (hF x) with ⟨e, hxe⟩
  exact ⟨e, Set.mem_univ e, hxe⟩

/-- The exact restriction to every edge is isomorphic to the original system
when the latter has no isolated vertices. -/
def edgeRestrictionUnivIso (hF : F.HasNoIsolatedPoints) :
    Iso (F.edgeRestriction Set.univ) F where
  vertexEquiv :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x, F.mem_edgeSupportSet_univ hF x⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => rfl }
  edgeEquiv :=
    { toFun := Subtype.val
      invFun := fun e => ⟨e, Set.mem_univ e⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => rfl }
  map_inc_iff := fun _ _ => Iff.rfl

end TripleSystem
end Erdos593
