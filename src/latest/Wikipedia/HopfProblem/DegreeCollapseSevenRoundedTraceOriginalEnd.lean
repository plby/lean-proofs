import Wikipedia.HopfProblem.DegreeCollapseSevenRoundedTraceBoundaryAtlas

/-!
# The original manifold is diffeomorphic to the native top boundary end

The boundary atlas here is the globally glued regular-zero atlas, not an
atlas chosen to force the conclusion. The forward map is smooth through
the actual cylinder boundary coordinates. The inverse is its original
manifold coordinate, with smoothness detected through the local
diffeomorphism from the cylinder boundary piece into the whole boundary.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def originalBoundaryHomeomorph : M ≃ₜ topBoundaryPart A :=
  (topEndHomeomorph A).trans (topEndBoundaryHomeomorph A)

def topBoundaryLift (m : M) : boundaryPieceDomain A .cylinder :=
  ⟨⟨topMap A m, topMap_isBoundaryPoint A m⟩, topMap_mem_cylinderOnly A m⟩

theorem topBoundaryLift_coordinates (m : M) :
    cylinderBoundaryCoordinates A (topBoundaryLift A m) = (m, UnroundedTrace.height A) :=
  topLift_coordinates A m

theorem contMDiff_topBoundaryLift : letI := boundaryPieceAtlas A .cylinder;
    ContMDiff (𝓡 7) (𝓡 7) ∞ (topBoundaryLift A) := by
  let := boundaryPieceAtlas A .cylinder
  apply (contMDiff_cylinderBoundary_iff_coordinates A _).mpr
  have he : cylinderBoundaryCoordinates A ∘ topBoundaryLift A =
      (fun m : M ↦ (m, UnroundedTrace.height A)) := funext (topBoundaryLift_coordinates A)
  rw [he]
  exact contMDiff_id.prodMk contMDiff_const

theorem contMDiff_originalBoundaryHomeomorph : letI := boundaryChartedSpace A;
    ContMDiff (𝓡 7) (𝓡 7) ∞ (originalBoundaryHomeomorph A) := by
  let := boundaryChartedSpace A
  let := boundaryPieceAtlas A .cylinder
  apply (ContMDiff.subtypeVal_comp_iff (topBoundaryPart A) (originalBoundaryHomeomorph A)).mp
  have hi : ContMDiff (𝓡 7) (𝓡 7) ∞
      (Subtype.val : boundaryPieceDomain A .cylinder → Boundary A) :=
    (boundaryOpenCover A).contMDiff_inclusion .cylinder
  exact hi.comp (contMDiff_topBoundaryLift A)

def topBoundaryCylinder (p : topBoundaryPart A) : boundaryPieceDomain A .cylinder :=
  ⟨p.val, ((mem_positiveCylinderPart_iff A p.val.val).mp p.property).choose⟩

theorem continuous_topBoundaryCylinder : Continuous (topBoundaryCylinder A) :=
  continuous_subtype_val.subtype_mk _

theorem contMDiff_topBoundaryCylinder : letI := boundaryChartedSpace A;
    letI := boundaryPieceAtlas A .cylinder;
    ContMDiff (𝓡 7) (𝓡 7) ∞ (topBoundaryCylinder A) := by
  let := boundaryChartedSpace A
  let := boundaryPieceAtlas A .cylinder
  intro p
  have hi := (boundaryOpenCover A).isLocalDiffeomorphAt_inclusion .cylinder
    (topBoundaryCylinder A p)
  exact (contMDiffAt_localDiffeomorph_comp_iff hi
    (continuous_topBoundaryCylinder A).continuousAt).mp
      (_root_.contMDiff_subtype_val (I := 𝓡 7) (U := topBoundaryPart A) (n := ∞)).contMDiffAt

theorem originalBoundaryHomeomorph_symm_coordinates (p : topBoundaryPart A) :
    (originalBoundaryHomeomorph A).symm p =
      (cylinderBoundaryCoordinates A (topBoundaryCylinder A p)).1 := by
  let m := (originalBoundaryHomeomorph A).symm p
  have he : (boundaryTracePoint A .cylinder (topBoundaryCylinder A p)).val =
      (topLift A m).val :=
    (congrArg (fun q : topBoundaryPart A ↦ q.val.val)
      ((originalBoundaryHomeomorph A).apply_symm_apply p)).symm
  have hq := Subtype.ext he
  change m = (unchangedCylinderHomeomorph A
    (boundaryTracePoint A .cylinder (topBoundaryCylinder A p))).val.val.1
  rw [hq, topLift_coordinates]

theorem contMDiff_originalBoundaryHomeomorph_symm : letI := boundaryChartedSpace A;
    ContMDiff (𝓡 7) (𝓡 7) ∞ (originalBoundaryHomeomorph A).symm := by
  let := boundaryChartedSpace A
  let := boundaryPieceAtlas A .cylinder
  have h := contMDiff_fst.comp ((contMDiff_cylinderBoundaryCoordinates A).comp
    (contMDiff_topBoundaryCylinder A))
  intro p
  exact (h p).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (originalBoundaryHomeomorph_symm_coordinates A))

def originalBoundaryDiffeomorph : letI := boundaryChartedSpace A;
    M ≃ₘ⟮𝓡 7, 𝓡 7⟯ topBoundaryPart A := by
  let := boundaryChartedSpace A
  exact
    { toEquiv := (originalBoundaryHomeomorph A).toEquiv
      contMDiff_toFun := contMDiff_originalBoundaryHomeomorph A
      contMDiff_invFun := contMDiff_originalBoundaryHomeomorph_symm A }

theorem originalBoundaryDiffeomorph_ambient (m : M) : letI := boundaryChartedSpace A;
    (originalBoundaryDiffeomorph A m).val.val.val =
      (HeightCylinder.heightCylinder e) (m, UnroundedTrace.height A) := rfl

theorem originalBoundaryDiffeomorph_frame (m : M) : letI := boundaryChartedSpace A;
    traceNormalFrame A (originalBoundaryDiffeomorph A m).val.val =
      boundaryFrameOperator (a.orthonormal m).val := traceNormalFrame_topMap A m

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace
