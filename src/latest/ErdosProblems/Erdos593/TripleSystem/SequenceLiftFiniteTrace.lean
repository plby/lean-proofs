import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseLetter
import ErdosProblems.Erdos593.TripleSystem.FiniteLinearImageTrace

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite canonical trace keys for sequence lifts

On every linear edge restriction, the canonical trace key from
`SequenceLiftBaseLetter` is injective.  This module records the resulting
extended-natural-cardinality, finite, and exact-natural-cardinality transfer.
In particular, the selected host edges of a finite linear source have one
canonical trace key per source edge.

The results are deliberately local to a specified linear restriction; they do
not assert global finiteness of arbitrary sequence-lift trace systems.
-/

namespace Erdos593

open scoped Cardinal Ordinal

universe u v w

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

/-- On a linear restriction, the canonical trace-key image is finite exactly
when the restriction itself is finite. -/
theorem traceKey_image_finite_iff_of_linear
    {S : Set (Edge G)}
    (hlin : ((system G).edgeRestriction S).Linear) :
    (traceKey '' S).Finite ↔ S.Finite := by
  constructor
  · intro himage
    exact Set.Finite.of_finite_image himage (traceKey_injOn_of_linear hlin)
  · intro hS
    exact hS.image traceKey

/-- On a linear restriction, canonical trace keys preserve extended natural
cardinality (`Set.encard`), including its finite/infinite distinction. -/
theorem traceKey_image_encard_eq_of_linear
    {S : Set (Edge G)}
    (hlin : ((system G).edgeRestriction S).Linear) :
    (traceKey '' S).encard = S.encard := by
  exact (traceKey_injOn_of_linear hlin).encard_image

/-- On a linear restriction, canonical trace keys preserve exact natural
cardinality.  For infinite restrictions the preceding `encard` theorem is the
nondegenerate formulation. -/
theorem ncard_traceKey_image_eq_of_linear
    {S : Set (Edge G)}
    (hlin : ((system G).edgeRestriction S).Linear) :
    (traceKey '' S).ncard = S.ncard := by
  exact (traceKey_injOn_of_linear hlin).ncard_image

/-- A finite linear source with no isolated points contributes exactly one
canonical trace key for each of its edge indices in any sequence lift. -/
theorem finiteLinear_traceKey_image
    {W : Type v} {E : Type w} {F : TripleSystem W E}
    [Fintype E]
    (f : F.Embedding (system G)) (hF : F.HasNoIsolatedPoints)
    (hlinear : F.Linear) :
    (traceKey '' f.edgeImage).Finite ∧
      (traceKey '' f.edgeImage).ncard = Fintype.card E := by
  have hlin : ((system G).edgeRestriction f.edgeImage).Linear :=
    f.imageEdgeRestriction_linear hF hlinear
  constructor
  · exact (Set.finite_range f.edge).image traceKey
  · calc
      (traceKey '' f.edgeImage).ncard = f.edgeImage.ncard :=
        (traceKey_injOn_of_linear hlin).ncard_image
      _ = (Set.range f.edge).ncard := rfl
      _ = Nat.card E := Set.ncard_range_of_injective f.edge_injective
      _ = Fintype.card E := Nat.card_eq_fintype_card

end SequenceLift

end Erdos593
