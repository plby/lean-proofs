import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiber

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Source indices for canonical sequence-lift base fibres

For an embedded source, a selected canonical base fibre is indexed by the
source edges whose images have that base node.  This module gives the exact
local cardinality bridge between the fibre, its base-letter image, and that
subtype of source-edge indices.  It deliberately does not assert a global
decomposition over all base nodes.
-/

namespace Erdos593

open scoped Cardinal Ordinal

universe u v w

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

/-- Source-edge indices whose embedded edge has canonical base node `q`. -/
abbrev baseFiberIndex
    {W : Type v} {E : Type w} {F : TripleSystem W E}
    (f : F.Embedding (system G)) (q : Node G) : Type w :=
  {i : E // baseNode (f.edge i) = q}

/-- The finite source-edge index subtype inherits a finite enumeration from a
finite source edge type.  It is kept explicit, rather than registered as a
global instance, so subsequent fibre-local statements choose their finite
enumeration transparently. -/
@[reducible]
noncomputable def baseFiberIndexFintype
    {W : Type v} {E : Type w} {F : TripleSystem W E}
    [Fintype E]
    (f : F.Embedding (system G)) (q : Node G) :
    Fintype (baseFiberIndex f q) :=
  Fintype.ofFinite _

/-- Under Lean's natural-cardinality convention (both sides are zero for an
infinite type), an embedded canonical base fibre has the cardinality of its
exact subtype of source-edge indices. -/
theorem ncard_baseFiber_edgeImage_eq_natCard_baseFiberIndex
    {W : Type v} {E : Type w} {F : TripleSystem W E}
    (f : F.Embedding (system G)) (q : Node G) :
    (baseFiber f.edgeImage q).ncard = Nat.card (baseFiberIndex f q) := by
  rw [baseFiber_edgeImage_eq_range]
  exact Set.ncard_range_of_injective (by
    intro i j hij
    apply Subtype.ext
    exact f.edge_injective hij)

/-- Extended natural cardinality preserves the full size of an embedded
canonical base fibre and its exact source-edge index subtype. -/
theorem encard_baseFiber_edgeImage_eq_baseFiberIndex
    {W : Type v} {E : Type w} {F : TripleSystem W E}
    (f : F.Embedding (system G)) (q : Node G) :
    (baseFiber f.edgeImage q).encard = ENat.card (baseFiberIndex f q) := by
  rw [baseFiber_edgeImage_eq_range]
  exact ENat.card_congr (Equiv.ofInjective _ (by
    intro i j hij
    apply Subtype.ext
    exact f.edge_injective hij)).symm

/-- On a linear embedded source image, the base-letter image of a selected
canonical base fibre has the full extended cardinality of its exact
source-edge index subtype. -/
theorem encard_baseLetter_image_eq_baseFiberIndex_of_linear
    {W : Type v} {E : Type w} {F : TripleSystem W E}
    (f : F.Embedding (system G)) (q : Node G)
    (hlin : ((system G).edgeRestriction f.edgeImage).Linear) :
    (baseLetter '' baseFiber f.edgeImage q).encard =
      ENat.card (baseFiberIndex f q) := by
  calc
    (baseLetter '' baseFiber f.edgeImage q).encard =
        (baseFiber f.edgeImage q).encard :=
      baseLetter_image_encard_eq_on_baseFiber_of_linear q hlin
    _ = ENat.card (baseFiberIndex f q) :=
      encard_baseFiber_edgeImage_eq_baseFiberIndex f q

/-- For a finite source, an embedded canonical base fibre has exactly as many
edges as its source-edge index subtype. -/
theorem baseFiber_edgeImage_ncard_eq_baseFiberIndex_card
    {W : Type v} {E : Type w} {F : TripleSystem W E}
    [Fintype E]
    (f : F.Embedding (system G)) (q : Node G) :
    (baseFiber f.edgeImage q).ncard =
      @Fintype.card (baseFiberIndex f q) (baseFiberIndexFintype f q) := by
  classical
  let : Fintype (baseFiberIndex f q) := baseFiberIndexFintype f q
  calc
    (baseFiber f.edgeImage q).ncard = Nat.card (baseFiberIndex f q) :=
      ncard_baseFiber_edgeImage_eq_natCard_baseFiberIndex f q
    _ = Fintype.card (baseFiberIndex f q) := Nat.card_eq_fintype_card

/-- For a finite linear source with no isolated points, the canonical
base-letter image at a selected base node has exactly the cardinality of the
corresponding source-edge index subtype. -/
theorem finiteLinear_baseLetter_image_ncard_eq_baseFiberIndex_card
    {W : Type v} {E : Type w} {F : TripleSystem W E}
    [Fintype E]
    (f : F.Embedding (system G)) (hF : F.HasNoIsolatedPoints)
    (hlinear : F.Linear) (q : Node G) :
    (baseLetter '' baseFiber f.edgeImage q).ncard =
      @Fintype.card (baseFiberIndex f q) (baseFiberIndexFintype f q) := by
  classical
  let : Fintype (baseFiberIndex f q) := baseFiberIndexFintype f q
  have hlin : ((system G).edgeRestriction f.edgeImage).Linear :=
    f.imageEdgeRestriction_linear hF hlinear
  calc
    (baseLetter '' baseFiber f.edgeImage q).ncard =
        (baseFiber f.edgeImage q).ncard :=
      ncard_baseLetter_image_eq_on_baseFiber_of_linear q hlin
    _ = Fintype.card (baseFiberIndex f q) :=
      baseFiber_edgeImage_ncard_eq_baseFiberIndex_card f q

end SequenceLift

end Erdos593
