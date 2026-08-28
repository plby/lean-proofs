import Wikipedia.HopfProblem.SpecialPeriodsThreefoldMeromorphicProjection
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldConnected
import Mathlib.Topology.LocalAtTarget

/-!
# Connected inverse images for genuine local meromorphic descent

An open continuous map with connected fibres has connected inverse
images of connected sets.  Restricting the actual map to such a set
gives a quotient map with the same literal fibres.  Applied to the
constructed sphere projection, this lets native meromorphic identity
extend a local factorization throughout a full base neighborhood.
-/

open Set Topology TopologicalSpace

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Connectedness of inverse images for open maps with connected
literal fibres.  No local trivialization is assumed. -/
theorem isConnected_preimage_of_open_connected_fibres
    (f : X → Y) (hf : Continuous f) (hopen : IsOpenMap f)
    (hfib : ∀ y : Y, IsConnected (f ⁻¹' {y})) {U : Set Y} (hU : IsConnected U) :
    IsConnected (f ⁻¹' U) := by
  let : ConnectedSpace U := isConnected_iff_connectedSpace.mp hU
  have hsurj : Function.Surjective f := fun y => (hfib y).nonempty
  have hrestricted : Continuous (U.restrictPreimage f) := hf.restrictPreimage
  have hquot : IsQuotientMap (U.restrictPreimage f) :=
    (hopen.restrictPreimage U).isQuotientMap hrestricted (hsurj.restrictPreimage U)
  have hfibU (y : U) : IsConnected ((U.restrictPreimage f) ⁻¹' {y}) := by
    refine ⟨hsurj.restrictPreimage U y, ?_⟩
    apply IsInducing.subtypeVal.isPreconnected_image.mp
    simpa only [image_val_preimage_restrictPreimage, image_singleton] using
      (hfib y.val).isPreconnected
  apply isConnected_iff_connectedSpace.mpr
  apply connectedSpace_iff_univ.mpr
  simpa only [preimage_univ] using
    hquot.isCoinducing.isConnected_preimage_of_isClosed hfibU isClosed_univ
      (isConnected_univ : IsConnected (univ : Set U))

end Wikipedia.HopfProblem.HolomorphicMeromorphic

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

/-- Full inverse images of connected native sphere neighborhoods are
connected in the original threefold, including all special fibres. -/
theorem projectionSphere_preimage_isConnected {U : Set RiemannSphere} (hU : IsConnected U) :
    IsConnected (projectionSphere ⁻¹' U) :=
  HolomorphicMeromorphic.isConnected_preimage_of_open_connected_fibres
    projectionSphere projectionSphere_continuous projectionSphere_isOpenMap
    projectionSphere_fibre_isConnected hU

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
