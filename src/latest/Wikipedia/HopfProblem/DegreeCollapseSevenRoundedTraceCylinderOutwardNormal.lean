import Wikipedia.HopfProblem.DegreeCollapseSevenRoundedTraceInducedBoundaryFrame
import Wikipedia.HopfProblem.DegreeCollapseSevenRoundedTraceOutwardCoorientation
import Wikipedia.NoExoticSixSphere.RoundedTraceCylinderOutwardNormal

/-! # Exact signs of the native outward normal at both cylinder ends -/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem cylinder_kernel_height_zero (p : boundaryPieceDomain A .cylinder)
    (v : Vector 7 × ℝ) (hv : cylinderBoundaryLevelDerivative A p v = 0) : v.2 = 0 := by
  have hd : cylinderBoundaryLevelDerivative A p v =
      (UnroundedTrace.height A - 2 * (cylinderBoundaryCoordinates A p).2) * v.2 :=
    IntervalSuperlevel.mfderiv_level_apply (I := 𝓡 7) (UnroundedTrace.height A)
      (cylinderBoundaryCoordinates A p) v
  have hn : UnroundedTrace.height A - 2 * (cylinderBoundaryCoordinates A p).2 ≠ 0 := by
    rcases cylinderBoundary_time_cases A p with ht | ht
    · rw [ht]
      linarith [UnroundedTrace.height_pos A]
    · rw [ht]
      linarith [UnroundedTrace.height_pos A]
  exact (mul_eq_zero.mp (hd.symm.trans hv)).resolve_left hn

theorem heightUnit_mem_cylinderBoundaryNormal (p : boundaryPieceDomain A .cylinder) :
    heightUnit e.ambientDimension ∈ (boundaryAmbientDerivative A p.val).rangeᗮ := by
  rw [boundaryTangent_cylinder]
  apply (Submodule.mem_orthogonal _ _).mpr
  rintro _ ⟨v, hv, rfl⟩
  have hz := cylinder_kernel_height_zero A p v hv
  let D : Vector 7 →L[ℝ] Vector e.ambientDimension :=
    mfderiv (𝓡 7) (𝓡 e.ambientDimension) e.toFun (cylinderBoundaryCoordinates A p).1
  have he : (HeightCylinder.heightCylinderDerivative e) (cylinderBoundaryCoordinates A p) v =
      coordinates e.ambientDimension 4 ((D v.1, v.2), 0) :=
    (HeightCylinder.heightCylinderDerivative_apply e) (cylinderBoundaryCoordinates A p) v
  change inner ℝ ((HeightCylinder.heightCylinderDerivative e) (cylinderBoundaryCoordinates A p) v)
    (heightUnit e.ambientDimension) = 0
  rw [he, heightUnit, inner_coordinates]
  simp [hz]

theorem pieceOutwardVector_cylinder (p : boundaryPieceDomain A .cylinder) :
    pieceOutwardVector A .cylinder p =
      (2 * (cylinderBoundaryCoordinates A p).2 - UnroundedTrace.height A) •
        heightUnit e.ambientDimension := by
  change (HeightCylinder.heightCylinderDerivative e) (cylinderBoundaryCoordinates A p)
    (0, 2 * (cylinderBoundaryCoordinates A p).2 - UnroundedTrace.height A) = _
  rw [(SevenSurgery.heightCylinderDerivative_vertical e), smul_heightUnit]

theorem pieceOutwardNormal_cylinder (p : boundaryPieceDomain A .cylinder) :
    pieceOutwardNormal A .cylinder p = NormedSpace.normalize
      ((2 * (cylinderBoundaryCoordinates A p).2 - UnroundedTrace.height A) •
        heightUnit e.ambientDimension) := by
  change NormedSpace.normalize
    (boundaryNormalProjection A p.val (pieceOutwardVector A .cylinder p)) = _
  rw [pieceOutwardVector_cylinder, boundaryNormalProjection_eq]
  rw [Submodule.starProjection_eq_self_iff.mpr
    (Submodule.smul_mem _ _ (heightUnit_mem_cylinderBoundaryNormal A p))]

theorem pieceOutwardNormal_cylinder_top (p : boundaryPieceDomain A .cylinder)
    (ht : (cylinderBoundaryCoordinates A p).2 = UnroundedTrace.height A) :
    pieceOutwardNormal A .cylinder p = heightUnit e.ambientDimension := by
  rw [pieceOutwardNormal_cylinder, ht, show 2 * UnroundedTrace.height A -
    UnroundedTrace.height A = UnroundedTrace.height A by ring,
    NormedSpace.normalize_smul_of_pos (UnroundedTrace.height_pos A),
    NormedSpace.normalize_eq_self_of_norm_eq_one (norm_heightUnit _)]

theorem pieceOutwardNormal_cylinder_bottom (p : boundaryPieceDomain A .cylinder)
    (ht : (cylinderBoundaryCoordinates A p).2 = 0) :
    pieceOutwardNormal A .cylinder p = -heightUnit e.ambientDimension := by
  rw [pieceOutwardNormal_cylinder, ht, mul_zero, zero_sub,
    NormedSpace.normalize_smul_of_neg (neg_neg_of_pos (UnroundedTrace.height_pos A)),
    NormedSpace.normalize_eq_self_of_norm_eq_one (norm_heightUnit _)]

theorem outwardNormal_originalBoundary (m : M) : letI := boundaryChartedSpace A;
    outwardNormal A (originalBoundaryDiffeomorph A m).val = heightUnit e.ambientDimension := by
  let := boundaryChartedSpace A
  change outwardNormal A (topBoundaryLift A m).val = _
  rw [outwardNormal_on_piece]
  exact pieceOutwardNormal_cylinder_top A (topBoundaryLift A m)
    (congrArg Prod.snd (topBoundaryLift_coordinates A m))

theorem inducedBoundaryFrame_originalBoundary (m : M) : letI := boundaryChartedSpace A;
    inducedBoundaryFrame A (originalBoundaryDiffeomorph A m).val =
      OrthogonalFrameAppend.operator (boundaryFrameOperator (a.orthonormal m).val)
        (heightUnit e.ambientDimension) := by
  let := boundaryChartedSpace A
  change OrthogonalFrameAppend.operator _ _ = _
  rw [originalBoundaryDiffeomorph_frame, outwardNormal_originalBoundary]

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace
