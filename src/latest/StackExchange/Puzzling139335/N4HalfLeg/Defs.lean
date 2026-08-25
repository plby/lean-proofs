import StackExchange.Puzzling139335.N4OuterPair.UpperNormals
import StackExchange.Puzzling139335.SourceFaceBridge.SupportingFaces

/-!
# Actual support-face spans for a half-height outer leg

Only two actual contact endpoints are needed for each face. They are
ordered by source height, and their vertical span is the horizontal
normal component times the physical square-side contact span.
-/

open Set

namespace Puzzling139335.N4HalfLeg

open SourceFaceBridge PlaneIsometries

/-- A positive source support span with a quantitative acute normal. -/
structure SourceFace (P : Set Plane) (c s : ℝ) where
  lower : Plane
  upper : Plane
  length : ℝ
  length_pos : 0 < length
  c_gt_four_fifths : (4 / 5 : ℝ) < c
  s_pos : 0 < s
  normal_unit : c ^ 2 + s ^ 2 = 1
  lower_support : SupportsAt P c s lower
  upper_support : SupportsAt P c s upper
  vertical_span : upper 1 - lower 1 = c * length

namespace SourceFace

variable {P : Set Plane} {c s : ℝ}

theorem c_pos (F : SourceFace P c s) : 0 < c := by
  linarith [F.c_gt_four_fifths]

theorem lower_mem (F : SourceFace P c s) : F.lower ∈ P := F.lower_support.1

theorem upper_mem (F : SourceFace P c s) : F.upper ∈ P := F.upper_support.1

end SourceFace

/-- The extrema of the actual right-side contact of a placed copy,
together with their source support span. -/
structure RightSpan (P Q : Set Plane) (e : Plane ≃ᵃⁱ[ℝ] Plane) where
  bottom : ℝ
  top : ℝ
  bottom_lt_top : bottom < top
  bottom_mem : Schoenflies.Plane.mk 1 bottom ∈ Q
  top_mem : Schoenflies.Plane.mk 1 top ∈ Q
  bounds : ∀ y : ℝ, Schoenflies.Plane.mk 1 y ∈ Q → y ∈ Icc bottom top
  face : SourceFace P (linearMatrix e 0 0) (linearMatrix e 0 1)
  length_eq : face.length = top - bottom

end Puzzling139335.N4HalfLeg
