import Wikipedia.NoExoticSixSphere.HalfLineCompactIntervals

/-!
# An open half-line region has no maximum or positive minimum

These statements use the actual relative half-line topology. Zero is the
only possible minimum; it is not silently treated as an interior real point.
-/

open Set Function Topology

namespace NoExoticSixSphere.HalfLineIntervals

open InvolutionQuotient

theorem exists_lt_in_open {V : Set HalfLine} (hV : IsOpen V)
    (y : HalfLine) (hy : y ∈ V) (hpos : 0 < y.val) :
    ∃ z ∈ V, z < y := by
  have hn : ¬ IsMin y := not_isMin_iff.mpr ⟨⟨0, le_rfl⟩, hpos⟩
  exact nonempty_nhds_inter_Iio (hV.mem_nhds hy) hn

theorem exists_gt_in_open {V : Set HalfLine} (hV : IsOpen V)
    (y : HalfLine) (hy : y ∈ V) : ∃ z ∈ V, y < z := by
  have hn : ¬ IsMax y := by
    apply not_isMax_iff.mpr
    refine ⟨⟨y.val + 1, by linarith [y.property]⟩, ?_⟩
    change y.val < y.val + 1
    linarith
  exact nonempty_nhds_inter_Ioi (hV.mem_nhds hy) hn

end NoExoticSixSphere.HalfLineIntervals
