import Wikipedia.NoExoticSixSphere.HalfLineOpenExtrema
import Wikipedia.NoExoticSixSphere.HalfLineLocalConnectivity

/-!
# Connected open intervals and strict interior bounds in the half-line

Every point of the relative interior is strictly below the upper endpoint.
A positive point is also strictly above the lower endpoint. These statements
retain the possible zero endpoint of the actual half-line topology.
-/

open Set Function Topology

namespace NoExoticSixSphere.HalfLineIntervals

open InvolutionQuotient

theorem coe_image_open_interval (a b : HalfLine) :
    (Subtype.val : HalfLine → ℝ) '' Ioo a b = Ioo a.val b.val := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, a.property.trans hx.1.le⟩, hx, rfl⟩

theorem isPreconnected_open_interval (a b : HalfLine) : IsPreconnected (Ioo a b) := by
  have hi : IsInducing (Subtype.val : HalfLine → ℝ) := ⟨rfl⟩
  apply hi.isPreconnected_image.mp
  rw [coe_image_open_interval]
  exact isPreconnected_Ioo

theorem isConnected_open_interval {a b : HalfLine} (hab : a < b) :
    IsConnected (Ioo a b) := ⟨nonempty_Ioo.mpr hab, isPreconnected_open_interval a b⟩

theorem interior_interval_lt_right {a b y : HalfLine} (hy : y ∈ interior (Icc a b)) :
    y < b := by
  obtain ⟨z, hz, hyz⟩ := exists_gt_in_open isOpen_interior y hy
  exact hyz.trans_le (interior_subset hz).2

theorem left_lt_interior_interval {a b y : HalfLine} (hy : y ∈ interior (Icc a b))
    (hpos : 0 < y.val) : a < y := by
  obtain ⟨z, hz, hzy⟩ := exists_lt_in_open isOpen_interior y hy hpos
  exact (interior_subset hz).1.trans_lt hzy

end NoExoticSixSphere.HalfLineIntervals
