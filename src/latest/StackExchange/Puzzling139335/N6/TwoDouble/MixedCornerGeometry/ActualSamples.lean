import StackExchange.Puzzling139335.N6.TwoDouble.MixedCornerGeometry.CornerData
import StackExchange.Puzzling139335.N6.TwoDouble.MixedCornerGeometry.HeightAvoidance
import StackExchange.Puzzling139335.N6.TwoDouble.MixedCornerGeometry.AxisSamples

/-!
# The normalized middle pieces have actual right-side samples

Six incidences make both left corners unique and both right corners double.
The height barriers exclude the other incident side away from the named
right corner. The Jordan axis-contact theorem then supplies the two points
needed for the relative-isometry classification.
-/

open Set

namespace Puzzling139335.N6.TwoDouble.MixedCornerGeometry

noncomputable section

open ReflectionSeparation

theorem normalized_right_side_samples (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 6)
    (hBL : corner 0 ∈ d.piece 0) (hBR : corner 1 ∈ d.piece 0)
    (hreflect : horizontal '' d.piece 0 = d.piece 1)
    (hH : corner 1 ∈ d.piece 2) (hG : corner 2 ∈ d.piece 3) :
    (∃ t : ℝ, 0 < t ∧ (!₂[(1 : ℝ), t] : Plane) ∈ d.piece 2) ∧
      ∃ u : ℝ, 0 < u ∧ (!₂[(1 : ℝ), 1 - u] : Plane) ∈ d.piece 3 := by
  have hcounts := normalized_mixed_corner_counts d hN hBR hreflect hH hG
  have hnotBL : corner 0 ∉ d.piece 2 :=
    N5.unique_corner_of_count_one d hcounts.1 hBL 2 (by decide)
  have hnotTL : corner 3 ∉ d.piece 3 :=
    N5.unique_corner_of_count_one d hcounts.2.2.2 (top_left_mem d hBL hreflect) 3
      (by decide)
  constructor
  · apply right_sample_at_bottom_of_avoidance d (by decide : (2 : Fin 4) ≠ 0) hH
    · intro l hl2 hl0
      exact other_not_mem_of_two_owners d (by decide : (2 : Fin 4) ≠ 0)
        hH hBR hcounts.2.1 hl2 hl0
    · intro p hp hy
      exact bottom_contact_eq_right d hc hBL hBR hreflect (by decide) hnotBL hp hy
  · apply right_sample_at_top_of_avoidance d (by decide : (3 : Fin 4) ≠ 1) hG
    · intro l hl3 hl1
      exact other_not_mem_of_two_owners d (by decide : (3 : Fin 4) ≠ 1)
        hG (top_right_mem d hBR hreflect) hcounts.2.2.1 hl3 hl1
    · intro p hp hy
      exact top_contact_eq_right d hc hBL hBR hreflect (by decide) hnotTL hp hy

end

end Puzzling139335.N6.TwoDouble.MixedCornerGeometry
