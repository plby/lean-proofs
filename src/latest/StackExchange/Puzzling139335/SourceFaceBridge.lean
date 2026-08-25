import StackExchange.Puzzling139335.SourceFaceBridge.ProperModel
import StackExchange.Puzzling139335.SourceFaceBridge.SupportingFaces
import StackExchange.Puzzling139335.SourceFaceBridge.Isometries
import StackExchange.Puzzling139335.SourceFaceBridge.Placements
import StackExchange.Puzzling139335.SourceFaceBridge.Frontier
import StackExchange.Puzzling139335.SourceFaceBridge.Contacts
import StackExchange.Puzzling139335.SourceFaceBridge.GlideBounds
import StackExchange.Puzzling139335.SourceFaceBridge.ProperObstruction
import StackExchange.Puzzling139335.SourceFaceBridge.GlideObstruction
import StackExchange.Puzzling139335.SourceFaceBridge.Flip
import StackExchange.Puzzling139335.SourceFaceBridge.EqualGlide
import StackExchange.Puzzling139335.SourceFaceBridge.UpperDefs
import StackExchange.Puzzling139335.SourceFaceBridge.SameSource
import StackExchange.Puzzling139335.SourceFaceBridge.NaturalSource
import StackExchange.Puzzling139335.SourceFaceBridge.ReversedSource

/-!
# From actual source geometry to the middle-piece obstruction

`SupportedSource` contains only explicit geometric inputs: the prototype's
lower-half-square containment, actual unit base and distinguished endpoint
memberships, acute source-normal parameters, and two affine images contained
in the unit square.  It contains no scalar crossing conclusion.

The finite scalar model, its strict crossing bounds, the actual frontier
segments, and their transverse intersection are all derived.  For a Jordan
prototype and two distinct actual common points, the proper placements have
overlapping interiors.  The same conclusion holds for glide placements,
without an angle-order or normal-gap assumption.

`UpperSupportedSource` permits arbitrary upper normals.  For distinct nonaxis
normals, the same-half-plane and natural-order exclusions are derived from
the actual endpoints and square containments, leaving the reversed case.
Deriving the source normalization, distinct nonaxis normals, and common-point
input from an arbitrary square dissection remains a separate global task.
-/

open Set

namespace Puzzling139335.SourceFaceBridge

namespace SupportedSource

variable {d : FaceData} {reversed : Bool} {P : Set Plane}

/-- The remaining normal gap and the actual source faces make the ordering
strict; no strict-angle assumption is added to the geometric model. -/
theorem strict_order_of_gap (h : SupportedSource d reversed P)
    (horder : d.β ≤ d.α)
    (hgap : Real.pi / 3 < Real.pi - d.α - d.β) : d.β < d.α := by
  have hm := h.toProperModel
  apply GlideCrossing.sourceFace_strict_order d.α d.β d.a d.b
    h.beta_pos horder h.alpha_lt_half_pi h.b_lt_half
  · have hh := hm.first_height
    change 2 * (1 / 2 - d.b) * Real.cos d.α ≤ 1 / 2 - d.a at hh
    nlinarith only [hh]
  · have hh := hm.second_height
    change 2 * (1 / 2 - d.a) * Real.cos d.β ≤ 1 / 2 - d.b at hh
    nlinarith only [hh]
  · exact hgap

/-- The ordered, large-normal-gap glide case contradicts disjoint Jordan
interiors, using two actual common points and the actual source base. -/
theorem ordered_glide_not_disjoint_interiors (h : SupportedSource d true P)
    (hP : IsJordanRegion P)
    (hcommon : ((d.right '' P) ∩ (d.leftGlide '' P)).Nontrivial)
    (horder : d.β ≤ d.α)
    (hgap : Real.pi / 3 < Real.pi - d.α - d.β) :
    ¬ Disjoint (interior (d.right '' P)) (interior (d.leftGlide '' P)) :=
  h.glide_not_disjoint_interiors hP (h.strict_order_of_gap horder hgap) hcommon

/-- Reflection exchanges the two source angles.  At equal angles the actual
image sets are disjoint, so the common-point hypothesis rules that case out. -/
theorem glide_not_disjoint_interiors_unordered (h : SupportedSource d true P)
    (hP : IsJordanRegion P)
    (hcommon : ((d.right '' P) ∩ (d.leftGlide '' P)).Nontrivial) :
    ¬ Disjoint (interior (d.right '' P)) (interior (d.leftGlide '' P)) := by
  rcases lt_trichotomy d.β d.α with hlt | heq | hgt
  · exact h.glide_not_disjoint_interiors hP hlt hcommon
  · exfalso
    obtain ⟨x, hx⟩ := hcommon.nonempty
    rw [h.equal_glide_intersection_eq_empty heq.symm] at hx
    exact hx
  · intro hdisjoint
    exact h.flip_glide.glide_not_disjoint_interiors
      (verticalReflection_isJordanRegion hP) hgt
      (d.flip_inter_nontrivial hcommon) (d.flip_disjoint_interiors hdisjoint)

/-- Concrete source geometry and a nontrivial actual interface contradict
disjoint Jordan interiors, for either relative placement parity. -/
theorem not_disjoint_interiors (h : SupportedSource d reversed P)
    (hP : IsJordanRegion P)
    (hcommon : ((d.right '' P) ∩ (d.left reversed '' P)).Nontrivial) :
    ¬ Disjoint (interior (d.right '' P)) (interior (d.left reversed '' P)) := by
  cases reversed
  · exact h.proper_not_disjoint_interiors hP hcommon
  · exact h.glide_not_disjoint_interiors_unordered hP hcommon

end SupportedSource

namespace UpperSupportedSource

variable {d : UpperFaceData} {reversed : Bool} {P : Set Plane}

/-- Actual endpoint support and inverse-square strips force the reversed
normal order.  No hull-variation inequalities are assumed. -/
theorem reversed_order_of_distinct_nonaxis (h : UpperSupportedSource d reversed P)
    (hφaxis : d.φ ≠ Real.pi / 2) (hψaxis : d.ψ ≠ Real.pi / 2)
    (hdistinct : d.φ ≠ d.ψ) : Real.pi / 2 < d.φ ∧ d.ψ < Real.pi / 2 := by
  rcases lt_or_gt_of_ne hφaxis with hφ | hφ
  · rcases lt_or_gt_of_ne hψaxis with hψ | hψ
    · exact (h.same_acute_false hφ hψ hdistinct).elim
    · exact (h.natural_straddle_false hφ hψ).elim
  · rcases lt_or_gt_of_ne hψaxis with hψ | hψ
    · exact ⟨hφ, hψ⟩
    · exact (h.same_obtuse_false hφ hψ hdistinct).elim

/-- The complete finite source-face obstruction for distinct nonaxis upper
normals, with either actual placement parity and an actual common interface. -/
theorem not_disjoint_interiors (h : UpperSupportedSource d reversed P)
    (hP : IsJordanRegion P)
    (hcommon : ((d.right '' P) ∩ (d.left reversed '' P)).Nontrivial)
    (hφaxis : d.φ ≠ Real.pi / 2) (hψaxis : d.ψ ≠ Real.pi / 2)
    (hdistinct : d.φ ≠ d.ψ) :
    ¬ Disjoint (interior (d.right '' P)) (interior (d.left reversed '' P)) := by
  obtain ⟨hφ, hψ⟩ := h.reversed_order_of_distinct_nonaxis hφaxis hψaxis hdistinct
  have hsource := h.toReversedSource hφ hψ
  have hcommon' :
      ((d.reversedData.right '' P) ∩ (d.reversedData.left reversed '' P)).Nontrivial := by
    simpa only [UpperFaceData.reversedData_right, UpperFaceData.reversedData_left] using hcommon
  simpa only [UpperFaceData.reversedData_right, UpperFaceData.reversedData_left] using
    hsource.not_disjoint_interiors hP hcommon'

end UpperSupportedSource

end Puzzling139335.SourceFaceBridge
