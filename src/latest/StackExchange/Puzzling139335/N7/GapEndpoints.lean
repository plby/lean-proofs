import StackExchange.Puzzling139335.N7.GapEndpoints.Exclusion
import StackExchange.Puzzling139335.N7.GapEndpoints.Segment
import Mathlib.Analysis.Convex.Topology

/-!
# The actual fourth piece contains the gap endpoints

The strict gap between the horizontal reflection and the third placement
lies in the fourth piece by the dissection cover. Its closed endpoints
also belong to that piece, since the piece is closed. No segment is
inferred from a convex hull or an assumed boundary sector.
-/

open Set

namespace Puzzling139335.N7

open ReflectionSeparation

theorem gap_openSegment_subset_fourth (d : SquareDissection) {c s : ℝ}
    (hs : 0 < s) (hsc : s < c) (hc : c ≤ 1) (hunit : c ^ 2 + s ^ 2 = 1)
    (hhalf : ∀ q ∈ d.piece 0, q 1 ≤ (1 / 2 : ℝ))
    (hH : horizontal '' d.piece 0 = d.piece 1)
    (hT : thirdMap c s '' d.piece 0 = d.piece 2)
    (hsupport : ∀ q ∈ d.piece 0, c * q 1 ≤ s * (1 - q 0)) :
    openSegment ℝ (gapLeft c s) (gapRight c s) ⊆ d.piece 3 := by
  intro p hp
  obtain ⟨hpsquare, _, hpheight, hgapH, hgapT⟩ :=
    gap_openSegment_properties hs hsc hc hp
  exact strict_gap_mem_fourth d hunit hhalf hH hT hsupport hpsquare
    (by linarith only [hpheight]) hgapH hgapT

/-- The entire closed gap segment belongs to the actual fourth piece. -/
theorem gap_segment_subset_fourth (d : SquareDissection) {c s : ℝ}
    (hs : 0 < s) (hsc : s < c) (hc : c ≤ 1) (hunit : c ^ 2 + s ^ 2 = 1)
    (hhalf : ∀ q ∈ d.piece 0, q 1 ≤ (1 / 2 : ℝ))
    (hH : horizontal '' d.piece 0 = d.piece 1)
    (hT : thirdMap c s '' d.piece 0 = d.piece 2)
    (hsupport : ∀ q ∈ d.piece 0, c * q 1 ≤ s * (1 - q 0)) :
    segment ℝ (gapLeft c s) (gapRight c s) ⊆ d.piece 3 := by
  exact segment_subset_closure_openSegment.trans
    (closure_minimal (gap_openSegment_subset_fourth d hs hsc hc hunit hhalf hH hT hsupport)
      (d.jordan 3).isClosed)

/-- Both gap endpoints are forced by actual cover and closedness. -/
theorem gap_endpoints_mem_fourth (d : SquareDissection) {c s : ℝ}
    (hs : 0 < s) (hsc : s < c) (hc : c ≤ 1) (hunit : c ^ 2 + s ^ 2 = 1)
    (hhalf : ∀ q ∈ d.piece 0, q 1 ≤ (1 / 2 : ℝ))
    (hH : horizontal '' d.piece 0 = d.piece 1)
    (hT : thirdMap c s '' d.piece 0 = d.piece 2)
    (hsupport : ∀ q ∈ d.piece 0, c * q 1 ≤ s * (1 - q 0)) :
    gapLeft c s ∈ d.piece 3 ∧ gapRight c s ∈ d.piece 3 := by
  have hsegment := gap_segment_subset_fourth d hs hsc hc hunit hhalf hH hT hsupport
  exact ⟨hsegment (left_mem_segment ℝ _ _), hsegment (right_mem_segment ℝ _ _)⟩

end Puzzling139335.N7
