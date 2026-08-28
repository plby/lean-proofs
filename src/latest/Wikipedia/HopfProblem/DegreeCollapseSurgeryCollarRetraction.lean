import Wikipedia.HopfProblem.DegreeCollapseSurgeryCornerEndpoint
import Wikipedia.HopfProblem.DegreeCollapseRoundedTraceHomotopyType
import Wikipedia.NoExoticSixSphere.UnitSurgeryComparisonSurjective

/-!
# The global rounding retraction has the exact native collar formula

On every actual collar point, the quotient deformation agrees with the
explicit coordinate deformation. On the old region this follows from
fixedness; on the added region it follows from the quotient computation,
using the actual collar chart's injectivity to recover its parameters.
Apply this to the native boundary collar and retain its exact endpoint.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.TraceRetraction

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization EuclideanEmbedding
open EuclideanEmbedding.FramedAttachingProduct
open EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
open NoExoticSixSphere.RoundedHandleCorner

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem deformation_sheet (t : I) (p : (Sphere 3 × Vector 3) × ℝ)
    (hv : p.1.2 ∈ ball (0 : Vector 3) A.radius) (ht : ‖p.2‖ ≤ collarHeight A)
    (hx : A.collarSheet p ∈ ambientSet A) :
    (deformation A (t, ⟨A.collarSheet p, hx⟩)).val =
      A.collarSheet (parameterDeform A (t : ℝ) p) := by
  rcases hx with hold | ⟨q, hq, hqp⟩
  · have hc := (sheet_mem_unrounded_iff A p.1.1 hv ht).mp hold
    have hp : parameterDeform A (t : ℝ) p = p := by
      unfold parameterDeform
      rw [CornerRetraction.deform_fixed_of_corner (UnroundedTrace.handleRadius_pos A).le hc]
    rw [hp]
    exact congrArg (fun z : ambientSet A ↦ z.val)
      (deformation_fixed A t ⟨A.collarSheet p, hold⟩)
  · have hsource : p ∈ A.tubeHeightCoordinates.source :=
      (A.mem_tubeHeightCoordinates_source p).mpr hv
    have he : q = p := A.injOn_collarSheet (addedParameters_subset_source A hq) hsource hqp
    subst q
    exact congrArg (fun z : ambientSet A ↦ z.val) (deformation_cover A t (Sum.inr ⟨p, hq⟩))

variable [IsManifold (𝓡 6) ∞ M]

theorem retraction_collarEndPoint (p : boundaryCollarParameters A) :
    (retraction A (UnitSurgery.collarEndPoint A p).val.val).val =
      A.collarSheet ((p.val.1,
        Real.sqrt ((UnroundedTrace.handleRadius A) ^ 2 + max p.val.2.2 0) • p.val.2.1.val),
        min p.val.2.2 0) := by
  let q := collarZeroPoint (bump A) (UnroundedTrace.handleRadius A) p.val
  have hp := (mem_boundaryCollarParameters_iff A p.val).mp p.property
  have hv : q.1.2 ∈ ball (0 : Vector 3) A.radius := by
    rw [mem_ball_zero_iff]
    change ‖(zeroPoint (bump A) (UnroundedTrace.handleRadius A) p.val.2).1‖ < A.radius
    rw [norm_zeroPoint_fst]
    exact hp.1
  have ht : ‖q.2‖ ≤ collarHeight A := by
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨hp.2.1.le, hp.2.2.le⟩
  have hx : A.collarSheet q ∈ ambientSet A :=
    (sheet_mem_iff A p.val.1 hv ht).mpr (level_zeroPoint (bump A)
      (UnroundedTrace.handleRadius A) p.val.2).ge
  have he : (UnitSurgery.collarEndPoint A p).val.val = ⟨A.collarSheet q, hx⟩ := by
    let := boundaryPieceAtlas A .collar
    exact Subtype.ext (boundaryCollarDiffeomorph_ambient A p)
  change (deformation A (1, (UnitSurgery.collarEndPoint A p).val.val)).val = _
  rw [he, deformation_sheet A 1 q hv ht hx]
  change A.collarSheet ((p.val.1,
    (CornerRetraction.deform (UnroundedTrace.handleRadius A) 1
      (zeroPoint (bump A) (UnroundedTrace.handleRadius A) p.val.2)).1),
    (CornerRetraction.deform (UnroundedTrace.handleRadius A) 1
      (zeroPoint (bump A) (UnroundedTrace.handleRadius A) p.val.2)).2) = _
  rw [CornerRetraction.deform_zeroPoint_one (bump A) (UnroundedTrace.handleRadius_pos A)]

end Wikipedia.HopfProblem.DegreeCollapse.TraceRetraction
