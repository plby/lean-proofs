import Wikipedia.HopfProblem.FibreTopology
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.LocalAtTarget

/-!
# Connected preimages under proper maps with connected fibres

Restriction to a full base preimage preserves closedness and identifies
the literal fibres homeomorphically.  The restricted map is therefore a
quotient map with connected fibres, giving connectedness over any connected
subset of the base.  No injectivity or local triviality is required.
-/

open Set Topology

namespace Wikipedia.HopfProblem.FibreTopology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/-- A continuous closed map with connected fibres pulls back every connected
subset to a connected subset, even when the base subset is not closed. -/
theorem isConnected_preimage_of_closed_of_connected_fibres
    (hf : Continuous f) (hclosed : IsClosedMap f)
    (hconn : ∀ y, IsConnected (f ⁻¹' {y})) {s : Set Y} (hs : IsConnected s) :
    IsConnected (f ⁻¹' s) := by
  have hsurj : Function.Surjective f := fun y => (hconn y).nonempty
  have hq : IsQuotientMap (s.restrictPreimage f) :=
    (hclosed.restrictPreimage s).isQuotientMap hf.restrictPreimage
      (hsurj.restrictPreimage s)
  have hlocal : ∀ y : s, IsConnected (s.restrictPreimage f ⁻¹' {y}) :=
    fun y => restrictPreimage_fibre_isConnected f s y (hconn y)
  let : ConnectedSpace s := isConnected_iff_connectedSpace.mp hs
  apply isConnected_iff_connectedSpace.mpr
  apply connectedSpace_iff_univ.mpr
  simpa only [preimage_univ] using
    hq.isCoinducing.isConnected_preimage_of_isClosed hlocal isClosed_univ
      (isConnected_univ : IsConnected (univ : Set s))

/-- Proper maps with connected fibres pull back all connected subsets to
connected subsets.  Fibre connectedness already implies surjectivity. -/
theorem isConnected_preimage_of_proper_of_connected_fibres
    (hproper : IsProperMap f) (hconn : ∀ y, IsConnected (f ⁻¹' {y}))
    {s : Set Y} (hs : IsConnected s) : IsConnected (f ⁻¹' s) :=
  isConnected_preimage_of_closed_of_connected_fibres
    hproper.continuous hproper.isClosedMap hconn hs

/-- Over an open connected base subset, the preimage is path connected when
the total space is locally path connected. -/
theorem isPathConnected_preimage_of_proper_of_connected_fibres
    [LocallyPathConnectedSpace X] (hproper : IsProperMap f)
    (hconn : ∀ y, IsConnected (f ⁻¹' {y})) {s : Set Y}
    (hsopen : IsOpen s) (hs : IsConnected s) : IsPathConnected (f ⁻¹' s) :=
  ((hsopen.preimage hproper.continuous).isConnected_iff_isPathConnected).mp
    (isConnected_preimage_of_proper_of_connected_fibres hproper hconn hs)

end Wikipedia.HopfProblem.FibreTopology
