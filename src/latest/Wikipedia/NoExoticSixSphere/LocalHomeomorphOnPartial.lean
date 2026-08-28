import Mathlib.Topology.IsLocalHomeomorph

/-!
# One original partial homeomorphism on an injective local-homeomorphism locus

Restriction to an open local-homeomorphism locus is a local homeomorphism.
Injectivity there gives a genuine partial homeomorphism with exactly the
original function and specified open source. This packages local tube
inverses without changing the map on their common neighborhood.
-/

noncomputable section

open Set Topology

namespace NoExoticSixSphere.LocalHomeomorphOnPartial

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (f : X → Y) (U : Set X) (hU : IsOpen U) (hf : IsLocalHomeomorphOn f U)

include hU hf in
/-- Actual restriction to the open locus retains its local inverse witnesses. -/
theorem local_domRestrict : IsLocalHomeomorph (U.domRestrict f) :=
  isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
    (hf.comp hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph.isLocalHomeomorphOn
      (show MapsTo (Subtype.val : U → X) Set.univ U from fun x _ => x.property))

variable [Nonempty X] (hi : InjOn f U)

/-- The specified original function on the specified original open source. -/
def partialHomeomorph : OpenPartialHomeomorph X Y :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict (hi.toPartialEquiv f U)
    hf.continuousOn (local_domRestrict f U hU hf).isOpenMap hU

theorem partialHomeomorph_source : (partialHomeomorph f U hU hf hi).source = U := rfl

theorem partialHomeomorph_apply (x : X) : partialHomeomorph f U hU hf hi x = f x := rfl

end NoExoticSixSphere.LocalHomeomorphOnPartial
