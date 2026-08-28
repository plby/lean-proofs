import Wikipedia.HopfProblem.DegreeCollapseLowRoundedTraceBoundaryParameterTangent

/-!

# Explicit outward directions for the actual three superlevel pieces

Every defining function is positive on the interior. These concrete tangent
vectors have strictly negative defining differential on the native boundary.
The collar direction uses the negative of the proved diagonal lift.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel LowRoundedHandleCorner

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M}
  (A : FramedAttachingProduct e a f)

def cylinderBoundaryLevelDerivative (p : boundaryPieceDomain A .cylinder) :
    (Vector 7 × ℝ) →L[ℝ] ℝ :=
  mfderiv ((𝓡 7).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
    (IntervalSuperlevel.level (M := M) (UnroundedTrace.height A)) (cylinderBoundaryCoordinates A p)

def collarBoundaryLevelDerivative (p : boundaryPieceDomain A .collar) :
    ((Vector d × Vector (7 - d)) × ℝ) →L[ℝ] ℝ :=
  mfderiv (collarModel d (7 - d)) 𝓘(ℝ, ℝ) (collarLevel (bump A) (UnroundedTrace.handleRadius A))
    (collarBoundaryCoordinates A p)

def cylinderOutwardDirection (p : boundaryPieceDomain A .cylinder) : Vector 7 × ℝ :=
  (0, 2 * (cylinderBoundaryCoordinates A p).2 - UnroundedTrace.height A)

def handleOutwardDirection (p : boundaryPieceDomain A .handle) : Vector (d + 1) × Vector (7 - d) :=
  (0, (handleBoundaryCoordinates A p).2)

def collarOutwardDirection (p : boundaryPieceDomain A .collar) : (Vector d × Vector (7 - d)) × ℝ :=
  ((0, (2 * ‖(collarBoundaryCoordinates A p).1.2‖ ^ 2)⁻¹ •
    (collarBoundaryCoordinates A p).1.2), -1)

theorem cylinderOutwardDirection_negative (p : boundaryPieceDomain A .cylinder) :
    cylinderBoundaryLevelDerivative A p (cylinderOutwardDirection A p) < 0 := by
  have hd : cylinderBoundaryLevelDerivative A p (cylinderOutwardDirection A p) =
      (UnroundedTrace.height A - 2 * (cylinderBoundaryCoordinates A p).2) *
        (cylinderOutwardDirection A p).2 :=
    IntervalSuperlevel.mfderiv_level_apply (I := 𝓡 7) (UnroundedTrace.height A)
      (cylinderBoundaryCoordinates A p) (cylinderOutwardDirection A p)
  rw [hd]
  change (UnroundedTrace.height A - 2 * (cylinderBoundaryCoordinates A p).2) *
    (2 * (cylinderBoundaryCoordinates A p).2 - UnroundedTrace.height A) < 0
  rcases cylinderBoundary_time_cases A p with hp | hp
  · rw [hp]
    nlinarith [UnroundedTrace.height_pos A]
  · rw [hp]
    nlinarith [UnroundedTrace.height_pos A]

theorem handleOutwardDirection_negative (p : boundaryPieceDomain A .handle) :
    fderiv ℝ (LowHandleSuperlevel.level (UnroundedTrace.handleRadius A))
      (handleBoundaryCoordinates A p) (handleOutwardDirection A p) < 0 := by
  rw [LowHandleSuperlevel.fderiv_level_apply]
  change -2 * inner ℝ (handleBoundaryCoordinates A p).2
    (handleBoundaryCoordinates A p).2 < 0
  rw [real_inner_self_eq_norm_sq]
  have hn := (LowHandleSuperlevel.zero_iff
    (UnroundedTrace.handleRadius_pos A) _).mp (handleBoundary_level_zero A p)
  rw [Metric.mem_sphere, dist_zero_right] at hn
  rw [hn]
  nlinarith [UnroundedTrace.handleRadius_pos A]

theorem collarOutwardDirection_differential (p : boundaryPieceDomain A .collar) :
    collarBoundaryLevelDerivative A p (collarOutwardDirection A p) = -2 := by
  let q := collarBoundaryCoordinates A p
  have hn : (collarProjection q).1 ≠ 0 :=
    GeneralRoundedHandleCorner.transverse_ne_zero_of_level_zero
      (bump A) (UnroundedTrace.handleRadius_pos A)
      (collarBoundary_level_zero A p)
  have hp : mfderiv (collarModel d (7 - d)) 𝓘(ℝ, Vector (7 - d) × ℝ) collarProjection q
      (collarOutwardDirection A p) =
        -GeneralRoundedHandleCorner.diagonalLift (collarProjection q) := by
    rw [mfderiv_collarProjection_apply]
    simp only [collarOutwardDirection, GeneralRoundedHandleCorner.diagonalLift,
      collarProjection, Prod.neg_mk, neg_smul, neg_neg, q]
    rfl
  have hc : collarBoundaryLevelDerivative A p =
      (fderiv ℝ (GeneralRoundedHandleCorner.level (bump A) (UnroundedTrace.handleRadius A))
        (collarProjection q)).comp
        (mfderiv (collarModel d (7 - d)) 𝓘(ℝ, Vector (7 - d) × ℝ) collarProjection q) := by
    rw [collarBoundaryLevelDerivative, collarLevel, mfderiv_comp q
      ((GeneralRoundedHandleCorner.contDiff_level (bump A)
        (UnroundedTrace.handleRadius A)).contMDiff.mdifferentiableAt (by simp))
      ((contMDiff_collarProjection (d := d) (q := 7 - d)).mdifferentiableAt (by simp)),
      mfderiv_eq_fderiv]
    rfl
  rw [hc]
  change fderiv ℝ (GeneralRoundedHandleCorner.level (bump A) (UnroundedTrace.handleRadius A))
    (collarProjection q) (mfderiv (collarModel d (7 - d)) 𝓘(ℝ, Vector (7 - d) × ℝ)
      collarProjection q (collarOutwardDirection A p)) = -2
  rw [hp, map_neg, GeneralRoundedHandleCorner.fderiv_level_diagonalLift
    (bump A) (UnroundedTrace.handleRadius A) hn]

theorem collarOutwardDirection_negative (p : boundaryPieceDomain A .collar) :
    collarBoundaryLevelDerivative A p (collarOutwardDirection A p) < 0 := by
  rw [collarOutwardDirection_differential]
  norm_num

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace
