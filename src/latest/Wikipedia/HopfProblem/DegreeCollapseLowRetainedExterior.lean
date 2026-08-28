import Wikipedia.HopfProblem.DegreeCollapseLowRoundedTraceBoundaryExterior
import Wikipedia.HopfProblem.DegreeCollapseLowInducedEndNormalFraming

/-!

# The retained original exterior inside the actual native complementary end

Reordering the open subtype layers identifies the cylinder boundary piece
with an open subset of the already constructed native complementary end.
The resulting diffeomorphism keeps the original manifold atlas and every
ambient point. Its trace columns and induced outward column retain their
exact original values, including the negative height sign at this end.
-/

noncomputable section

open Function Set Topology TopologicalSpace
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [CompactSpace M] [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M} (A : FramedAttachingProduct e a f)

def nativeExteriorPart : Opens (otherBoundaryPart A) :=
  ⟨Subtype.val ⁻¹' boundaryPieceDomain A .cylinder,
    (boundaryPieceDomain A .cylinder).isOpen.preimage continuous_subtype_val⟩

def nativeExteriorReorder : bottomCylinderBoundaryPart A ≃ₜ nativeExteriorPart A where
  toFun p := ⟨⟨p.val.val, p.property⟩, p.val.property⟩
  invFun p := ⟨⟨p.val.val, p.property⟩, p.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

def exteriorNativeHomeomorph : retainedExterior A ≃ₜ nativeExteriorPart A := by
  let := boundaryPieceAtlas A .cylinder
  exact (exteriorBoundaryDiffeomorph A).toHomeomorph.trans (nativeExteriorReorder A)

def nativeExteriorCylinder (p : nativeExteriorPart A) : boundaryPieceDomain A .cylinder :=
  ⟨p.val.val, p.property⟩

theorem continuous_nativeExteriorCylinder : Continuous (nativeExteriorCylinder A) :=
  (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

theorem contMDiff_nativeExteriorCylinder : letI := boundaryChartedSpace A;
    letI := boundaryPieceAtlas A .cylinder;
    ContMDiff (𝓡 7) (𝓡 7) ∞ (nativeExteriorCylinder A) := by
  let := boundaryChartedSpace A
  let := boundaryPieceAtlas A .cylinder
  intro p
  have hi := (boundaryOpenCover A).isLocalDiffeomorphAt_inclusion .cylinder
    (nativeExteriorCylinder A p)
  apply (contMDiffAt_localDiffeomorph_comp_iff hi
    (continuous_nativeExteriorCylinder A).continuousAt).mp
  exact ((_root_.contMDiff_subtype_val (I := 𝓡 7) (U := otherBoundaryPart A) (n := ∞)).comp
    (_root_.contMDiff_subtype_val (I := 𝓡 7) (U := nativeExteriorPart A) (n := ∞))).contMDiffAt

theorem contMDiff_exteriorNativeHomeomorph : letI := boundaryChartedSpace A;
    ContMDiff (𝓡 7) (𝓡 7) ∞ (exteriorNativeHomeomorph A) := by
  let := boundaryChartedSpace A
  let := boundaryPieceAtlas A .cylinder
  apply (ContMDiff.subtypeVal_comp_iff (nativeExteriorPart A)
    (exteriorNativeHomeomorph A)).mp
  apply (ContMDiff.subtypeVal_comp_iff (otherBoundaryPart A) _).mp
  have hi : ContMDiff (𝓡 7) (𝓡 7) ∞
      (Subtype.val : boundaryPieceDomain A .cylinder → Boundary A) :=
    (boundaryOpenCover A).contMDiff_inclusion .cylinder
  exact hi.comp ((_root_.contMDiff_subtype_val (I := 𝓡 7)
    (U := bottomCylinderBoundaryPart A) (n := ∞)).comp
      (contMDiff_exteriorBottomBoundaryMap A))

theorem exteriorNativeHomeomorph_symm_coordinates (p : nativeExteriorPart A) :
    ((exteriorNativeHomeomorph A).symm p).val =
      (cylinderBoundaryCoordinates A (nativeExteriorCylinder A p)).1 := rfl

theorem contMDiff_exteriorNativeHomeomorph_symm : letI := boundaryChartedSpace A;
    ContMDiff (𝓡 7) (𝓡 7) ∞ (exteriorNativeHomeomorph A).symm := by
  let := boundaryChartedSpace A
  let := boundaryPieceAtlas A .cylinder
  apply (ContMDiff.subtypeVal_comp_iff (retainedExterior A)
    (exteriorNativeHomeomorph A).symm).mp
  exact contMDiff_fst.comp ((contMDiff_cylinderBoundaryCoordinates A).comp
    (contMDiff_nativeExteriorCylinder A))

def exteriorNativeDiffeomorph : letI := boundaryChartedSpace A;
    retainedExterior A ≃ₘ⟮𝓡 7, 𝓡 7⟯ nativeExteriorPart A := by
  let := boundaryChartedSpace A
  exact
    { toEquiv := (exteriorNativeHomeomorph A).toEquiv
      contMDiff_toFun := contMDiff_exteriorNativeHomeomorph A
      contMDiff_invFun := contMDiff_exteriorNativeHomeomorph_symm A }

theorem exteriorNativeDiffeomorph_ambient (m : retainedExterior A) :
    letI := boundaryChartedSpace A;
    (exteriorNativeDiffeomorph A m).val.val.val.val =
      LowHeightCylinder.heightCylinder d e (m.val, 0) := rfl

theorem traceNormalFrame_exteriorNative (m : retainedExterior A) :
    letI := boundaryChartedSpace A;
    traceNormalFrame A (exteriorNativeDiffeomorph A m).val.val.val =
      boundaryFrameOperator d (a.orthonormal m.val).val := by
  let := boundaryChartedSpace A
  have h := traceNormalFrame_on_piece A .cylinder (exteriorCylinderLift A m)
  change traceNormalFrame A (exteriorNativeDiffeomorph A m).val.val.val = _ at h
  rw [h]
  change boundaryFrameOperator d
    (a.orthonormal (unchangedCylinderHomeomorph A (exteriorCylinderLift A m)).val.val.1).val = _
  rw [exteriorCylinderLift_coordinates]

theorem outwardNormal_exteriorNative (m : retainedExterior A) :
    letI := boundaryChartedSpace A;
    outwardNormal A (exteriorNativeDiffeomorph A m).val.val =
      -heightUnit d e.ambientDimension := by
  let := boundaryChartedSpace A
  change outwardNormal A (exteriorBoundaryLift A m).val = _
  rw [outwardNormal_on_piece]
  exact pieceOutwardNormal_cylinder_bottom A (exteriorBoundaryLift A m)
    (congrArg Prod.snd (exteriorBoundaryLift_coordinates A m))

theorem inducedBoundaryFrame_exteriorNative (m : retainedExterior A) :
    letI := boundaryChartedSpace A;
    inducedBoundaryFrame A (exteriorNativeDiffeomorph A m).val.val =
      OrthogonalFrameAppend.operator (boundaryFrameOperator d (a.orthonormal m.val).val)
        (-heightUnit d e.ambientDimension) := by
  let := boundaryChartedSpace A
  change OrthogonalFrameAppend.operator _ _ = _
  rw [traceNormalFrame_exteriorNative, outwardNormal_exteriorNative]

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace
