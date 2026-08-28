import Wikipedia.HopfProblem.DegreeCollapseLowSurgeryTimePieces
import Wikipedia.NoExoticSixSphere.SmoothOpenCoverRestriction

/-!

# Smoothness of the constructed time in the existing native end atlas

Restrict the original smooth boundary open cover to the complementary end.
The cylinder formula is the original smooth profile in its native original
coordinates, and the other two formulas are constant. This proves global
smoothness without transporting an atlas through the closed-piece map.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.NativeSurgery

open NoExoticSixSphere GLOrthonormalization RoundedTrace SurgeryPair

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [CompactSpace M] [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M} (A : FramedAttachingProduct e a f)
  (hR : A.radius = 2) (T : TimeData A)

theorem contMDiff_timeFunction : letI := boundaryChartedSpace A;
    ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ (timeFunction A hR T) := by
  let := boundaryChartedSpace A
  apply ((boundaryOpenCover A).contMDiff_onOpen_iff (otherBoundaryPart A) _).mpr
  intro i
  cases i with
  | cylinder =>
      let := boundaryPieceAtlas A .cylinder
      have he : timeFunction A hR T ∘ SmoothOpenCover.restrictedInclusion
          (U := boundaryPieceDomain A) (otherBoundaryPart A) .cylinder =
          (fun p : bottomCylinderBoundaryPart A ↦
            oldProfile A T (cylinderBoundaryCoordinates A p.val).1) :=
        funext (timeFunction_cylinder A hR T)
      rw [he]
      exact (contMDiff_oldProfile A T).comp
        (contMDiff_fst.comp ((contMDiff_cylinderBoundaryCoordinates A).comp
          (_root_.contMDiff_subtype_val (U := bottomCylinderBoundaryPart A))))
  | handle =>
      let := boundaryPieceAtlas A .handle
      have he : timeFunction A hR T ∘ SmoothOpenCover.restrictedInclusion
          (U := boundaryPieceDomain A) (otherBoundaryPart A) .handle =
          (fun _ ↦ (1 : ℝ)) := by
        funext p
        exact timeFunction_handle A hR T _ p.val.property
      rw [he]
      exact contMDiff_const
  | collar =>
      let := boundaryPieceAtlas A .collar
      have he : timeFunction A hR T ∘ SmoothOpenCover.restrictedInclusion
          (U := boundaryPieceDomain A) (otherBoundaryPart A) .collar =
          (fun _ ↦ (1 : ℝ)) := by
        funext p
        exact timeFunction_collar A hR T _ p.val.property
      rw [he]
      exact contMDiff_const

def exteriorMap (m : retainedExterior A) : otherBoundaryPart A :=
  (exteriorNativeHomeomorph A m).val

theorem isOpenEmbedding_exteriorMap : IsOpenEmbedding (exteriorMap A) :=
  (nativeExteriorPart A).isOpen.isOpenEmbedding_subtypeVal.comp
    (exteriorNativeHomeomorph A).isOpenEmbedding

theorem contMDiff_exteriorMap : letI := boundaryChartedSpace A;
    ContMDiff (𝓡 7) (𝓡 7) ∞ (exteriorMap A) := by
  let := boundaryChartedSpace A
  exact (_root_.contMDiff_subtype_val (I := 𝓡 7) (U := nativeExteriorPart A)).comp
    (exteriorNativeDiffeomorph A).contMDiff_toFun

theorem timeFunction_exteriorMap (m : retainedExterior A) :
    timeFunction A hR T (exteriorMap A m) = oldProfile A T m.val :=
  timeFunction_nativeExterior A hR T m

theorem exteriorMap_ambient (m : retainedExterior A) :
    (exteriorMap A m).val.val.val = LowHeightCylinder.heightCylinder d e (m.val, 0) := rfl

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.NativeSurgery
