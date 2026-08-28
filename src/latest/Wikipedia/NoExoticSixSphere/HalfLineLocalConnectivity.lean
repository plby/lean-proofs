import Wikipedia.NoExoticSixSphere.HalfLineCompactIntervals
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Order.IntermediateValue

/-!
# Local connectedness of the actual half-line model

Every neighborhood contains one of the constructed compact intervals as a
smaller neighborhood. These intervals are connected in the existing subtype
topology, by their genuine inclusion into the corresponding real interval.
-/

open Set Function Topology

namespace NoExoticSixSphere.HalfLineIntervals

open InvolutionQuotient

theorem isPreconnected_interval (a b : HalfLine) : IsPreconnected (Icc a b) := by
  have hi : IsInducing (Subtype.val : HalfLine → ℝ) := ⟨rfl⟩
  apply hi.isPreconnected_image.mp
  rw [coe_image_interval]
  exact isPreconnected_Icc

theorem halfLineLocallyConnected : LocallyConnectedSpace HalfLine := by
  apply locallyConnectedSpace_iff_connected_subsets.mpr
  intro x U hU
  obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.mp hU
  obtain ⟨a, b, hab, hxI, hIV⟩ := exists_interval_in_open hV x hxV
  exact ⟨Icc a b, mem_interior_iff_mem_nhds.mp hxI, isPreconnected_interval a b,
    hIV.trans hVU⟩

attribute [instance] halfLineLocallyConnected

end NoExoticSixSphere.HalfLineIntervals
