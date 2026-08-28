import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCuspPullbackRegularCoordinates

/-!
# Actual period-quotient derivatives for the elliptic comparison

The native period quotient is a local biholomorphism. Its differential has
determinant one over a common-coordinate base, because its local coordinate
expression is a lattice shear. The generic shear calculation is shared with
the cusp comparison; here it is recorded for arbitrary alternating top covectors.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticComparison

open TrianglePeriodFamily.Canonical

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "I₃" => modelWithCornersSelf ℂ Model

variable {B : Type*} [TopologicalSpace B] [ChartedSpace ℂ B]
    [IsManifold I₁ ω B]

local instance periodProductChartedSpace : ChartedSpace Model (B × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (B × ComplexPlane₂))

local instance periodProductManifold : IsManifold I₃ ω (B × ComplexPlane₂) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := I₁) (I' := I₂) B ComplexPlane₂

/-- The original complex period projection is locally biholomorphic in its native atlas. -/
theorem periodQuotient_isLocalDiffeomorph (P : HolomorphicPeriodMap ℂ B) :
    letI := P.totalChartedSpace
    IsLocalDiffeomorph I₃ I₃ ω P.quotientMap := by
  let := P.totalChartedSpace
  let := P.coveringAction
  exact CoveringQuotient.project_isLocalDiffeomorph
    P.quotientCoveringMap P.coveringAction_holomorphic

variable (coordinate : B → ℂ) (hcoordinate : ∀ a x : B, chartAt ℂ a x = coordinate x)

include hcoordinate in
/-- Actual pullback of the full base-first alternating volume by the period quotient. -/
theorem periodQuotient_volume_pullback (P : HolomorphicPeriodMap ℂ B)
    (x : B × ComplexPlane₂) :
    letI := P.totalChartedSpace
    volume.compContinuousLinearMap (mfderiv I₃ I₃ P.quotientMap x) = volume :=
  GlobalCuspPullback.periodQuotient_volume_pullback coordinate hcoordinate P x

include hcoordinate in
/-- Determinant one for the original manifold derivative, not an assumed chart label. -/
theorem periodQuotient_det (P : HolomorphicPeriodMap ℂ B) (x : B × ComplexPlane₂) :
    letI := P.totalChartedSpace
    LinearMap.det (mfderiv I₃ I₃ P.quotientMap x).toLinearMap = 1 := by
  let := P.totalChartedSpace
  have h := congrArg (fun α : TopCovector => coefficient α)
    (periodQuotient_volume_pullback coordinate hcoordinate P x)
  have hd := (coefficient_pullback volume
    (mfderiv I₃ I₃ P.quotientMap x : Model →L[ℂ] Model)).symm.trans h
  simp only [coefficient_volume, mul_one] at hd
  exact hd

include hcoordinate in
/-- Every genuine alternating three-covector is unchanged by this native differential. -/
theorem periodQuotient_topCovector_pullback (P : HolomorphicPeriodMap ℂ B)
    (α : TopCovector) (x : B × ComplexPlane₂) :
    letI := P.totalChartedSpace
    α.compContinuousLinearMap (mfderiv I₃ I₃ P.quotientMap x) = α := by
  let := P.totalChartedSpace
  exact (pullback_eq_det_smul α (mfderiv I₃ I₃ P.quotientMap x)).trans
    ((congrArg (fun c : ℂ => c • α)
      (periodQuotient_det coordinate hcoordinate P x)).trans (one_smul ℂ α))

include hcoordinate in
/-- Pullback of the actual canonical-bundle volume section on the varying period family. -/
theorem familyVolume_periodQuotient_pullback (P : HolomorphicPeriodMap ℂ B)
    (x : B × ComplexPlane₂) :
    letI := P.totalChartedSpace
    (familyCanonicalIntrinsicEquiv P (P.quotientMap x)
      (familyCanonicalVolume P (P.quotientMap x))).compContinuousLinearMap
        (mfderiv I₃ I₃ P.quotientMap x) = volume :=
  GlobalCuspPullback.familyVolume_periodQuotient_pullback coordinate hcoordinate P x

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticComparison
