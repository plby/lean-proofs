import StackExchange.Puzzling139335.SourceFaceBridge.Contacts
import StackExchange.Puzzling139335.SourceFaceBridge.Frontier
import StackExchange.Puzzling139335.SourceFaceBridge.Isometries
import StackExchange.Puzzling139335.SourceFaceBridge.Placements
import StackExchange.Puzzling139335.SegmentCrossing
import StackExchange.Puzzling139335.JordanTransport

/-!
# The actual proper placements have intersecting interiors

The scalar contact theorem places the Cramer parameters strictly inside the
actual unit bases. Their determinant is nonzero. Once these bases are put
in the actual frontiers, the Jordan-region crossing theorem applies.
-/

open Set

namespace Puzzling139335.SourceFaceBridge

namespace FaceData

/-- The affine parameter on the right image base is the actual image of
the corresponding source base point. -/
theorem proper_right_segment_point (d : FaceData) (t : ℝ) :
    SegmentCrossing.point (d.right (point 0 0)) (d.right (point 1 0)) t =
      d.right (point t 0) := by
  apply point_ext <;> simp [SegmentCrossing.point, right_base]
  all_goals ring

/-- The affine parameter on the left proper image base has the same
source parameter. -/
theorem proper_left_segment_point (d : FaceData) (t : ℝ) :
    SegmentCrossing.point (d.leftProper (point 0 0)) (d.leftProper (point 1 0)) t =
      d.leftProper (point t 0) := by
  apply point_ext <;> simp [SegmentCrossing.point, leftProper_base]
  all_goals ring

/-- The determinant of the actual, untransformed image bases is the
negative sum-angle sine from the scalar model. -/
theorem proper_base_determinant (d : FaceData) :
    SegmentCrossing.det (d.right (point 1 0) - d.right (point 0 0))
      (d.leftProper (point 1 0) - d.leftProper (point 0 0)) = -d.scalarData.delta := by
  simp only [right_base, leftProper_base, SegmentCrossing.det, PiLp.sub_apply,
    point_zero, point_one, ProperRotation.Data.delta]
  ring

/-- Cramer's equality from the scalar model is an equality of points on
the original two image bases, without assuming any overlap. -/
theorem proper_base_intersection (d : FaceData) (hdelta : d.scalarData.delta ≠ 0) :
    SegmentCrossing.point (d.right (point 0 0)) (d.right (point 1 0))
        (d.scalarData.ns / d.scalarData.delta) =
      SegmentCrossing.point (d.leftProper (point 0 0)) (d.leftProper (point 1 0))
        (d.scalarData.nt / d.scalarData.delta) := by
  have hp := d.scalarData.intersection_point_eq hdelta
  have hx := congrArg Prod.fst hp
  have hy := congrArg Prod.snd hp
  rw [proper_right_segment_point, proper_left_segment_point, right_base, leftProper_base]
  apply point_ext
  · change 1 - d.scalarData.u - (d.scalarData.ns / d.scalarData.delta) * d.scalarData.c =
      d.scalarData.w - (d.scalarData.nt / d.scalarData.delta) * d.scalarData.d
    linarith only [hx]
  · change 1 / 2 - d.scalarData.v - (d.scalarData.ns / d.scalarData.delta) * d.scalarData.s =
      1 / 2 + d.scalarData.z + (d.scalarData.nt / d.scalarData.delta) * d.scalarData.q
    linarith only [hy]

end FaceData

namespace SupportedSource

/-- The normalized supported proper placements of a Jordan region cannot
have disjoint interiors if their actual common set contains two points. -/
theorem proper_not_disjoint_interiors {d : FaceData} {P : Set Plane}
    (h : SupportedSource d false P) (hP : IsJordanRegion P)
    (hcommon : (d.right '' P ∩ d.leftProper '' P).Nontrivial) :
    ¬ Disjoint (interior (d.right '' P)) (interior (d.leftProper '' P)) := by
  have hright : IsJordanRegion (d.right '' P) :=
    hP.image_homeomorph d.rightIsometry.toHomeomorph
  have hleft : IsJordanRegion (d.leftProper '' P) :=
    hP.image_homeomorph d.leftProperIsometry.toHomeomorph
  have hdelta : d.scalarData.delta ≠ 0 := h.toProperModel.delta_pos.ne'
  have hdet : SegmentCrossing.det
      (d.right (point 1 0) - d.right (point 0 0))
      (d.leftProper (point 1 0) - d.leftProper (point 0 0)) ≠ 0 := by
    rw [d.proper_base_determinant]
    exact neg_ne_zero.mpr hdelta
  obtain ⟨ht0, ht1, hu0, hu1⟩ := h.proper_strict_intersection_parameters hcommon
  exact SegmentCrossing.not_disjoint_interiors_of_point_eq hright hleft
    h.right_base_frontier h.leftProper_base_frontier hdet
    ⟨ht0, ht1⟩ ⟨hu0, hu1⟩ (d.proper_base_intersection hdelta)

end SupportedSource

end Puzzling139335.SourceFaceBridge
