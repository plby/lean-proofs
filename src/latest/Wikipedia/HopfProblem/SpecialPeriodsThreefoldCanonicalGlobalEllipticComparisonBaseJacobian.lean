import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalEllipticComparisonBaseUnits
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalRegularBaseDerivatives
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticJacobianLift

/-!
# The actual elliptic-to-regular base differential comparison

The ambient derivative of the finite sphere coordinate is its native
manifold derivative on the disc.  The actual punctured root lift gives
the same finite coordinate as the original regular covering.  Applying
the genuine manifold chain rule, with the identity derivatives of the
two open inclusions, gives the required elliptic base-Jacobian factor.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticComparison

open HolomorphicDifferentialForms

local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- The ambient derivative is the actual native differential of the finite
sphere coordinate on the original disc, not a separately assigned factor. -/
theorem baseDerivative_eq_mfderiv (j : Elliptic.Kind) (s : Disc) :
    baseDerivative j (s : ℂ) =
      (show ℂ →L[ℂ] ℂ from mfderiv I₁ I₁ (discCoordinate j) s) 1 := by
  rw [((discCoordinate_holomorphic j s).mdifferentiableAt (by simp)).mfderiv]
  simp only [writtenInExtChartAt, mfld_simps, fderivWithin_univ, chartAt_self_eq]
  rfl

/-- The actual derivative comparison on the original punctured root domain. -/
theorem baseDerivative_eq_regularCoordinateDerivative_mul_baseJacobian
    (j : Elliptic.Kind) (s : HolomorphicForms.EllipticCover.RootStar j) :
    baseDerivative j (s.val.val : ℂ) =
      GlobalRegular.coordinateDerivative (HolomorphicForms.EllipticCover.regularBase j s) *
        HolomorphicForms.EllipticCover.baseJacobian j s.val := by
  let Ld : ℂ →L[ℂ] ℂ := mfderiv I₁ I₁ (discCoordinate j) s.val.val
  let Lt : ℂ →L[ℂ] ℂ := mfderiv I₁ I₁ GlobalRegular.upstairsCoordinate
    (HolomorphicForms.EllipticCover.regularBase j s)
  let Lb : ℂ →L[ℂ] ℂ := mfderiv I₁ I₁ (HolomorphicForms.EllipticCover.regularBase j) s
  have hi :=
    (hasMFDerivAt_openSubtypeVal (E := ℂ)
      (HolomorphicForms.EllipticCover.rootDomain j) s.val).comp s
      (hasMFDerivAt_openSubtypeVal (E := ℂ)
        (HolomorphicForms.EllipticCover.rootStarDomain j) s)
  have hd : HasMFDerivAt I₁ I₁ (discCoordinate j) s.val.val Ld :=
    ((discCoordinate_holomorphic j s.val.val).mdifferentiableAt (by simp)).hasMFDerivAt
  have hdisc := hd.comp s hi
  have hu : HasMFDerivAt I₁ I₁ GlobalRegular.upstairsCoordinate
      (HolomorphicForms.EllipticCover.regularBase j s) Lt :=
    ((GlobalRegular.upstairsCoordinate_holomorphic _).mdifferentiableAt
      (by simp)).hasMFDerivAt
  have hb : HasMFDerivAt I₁ I₁ (HolomorphicForms.EllipticCover.regularBase j) s Lb :=
    ((HolomorphicForms.EllipticCover.regularBase_holomorphic j s).mdifferentiableAt
      (by simp)).hasMFDerivAt
  have ht := hu.comp s hb
  have he' : Ld.comp ((ContinuousLinearMap.id ℂ ℂ).comp (ContinuousLinearMap.id ℂ ℂ)) =
      Lt.comp Lb := hdisc.mfderiv.symm.trans ht.mfderiv
  have he : Ld = Lt.comp Lb := by
    simpa only [ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id] using he'
  rw [baseDerivative_eq_mfderiv, GlobalRegular.coordinateDerivative_eq_mfderiv]
  change Ld 1 = Lt 1 * HolomorphicForms.EllipticCover.baseJacobian j s.val
  rw [he]
  change Lt (Lb 1) = Lt 1 * HolomorphicForms.EllipticCover.baseJacobian j s.val
  rw [show Lb 1 = HolomorphicForms.EllipticCover.baseJacobian j s.val from
    HolomorphicForms.EllipticCover.mfderiv_regularBase_one j s]
  simpa only [smul_eq_mul, mul_one, one_mul, mul_comm] using
    Lt.map_smul (HolomorphicForms.EllipticCover.baseJacobian j s.val) (1 : ℂ)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticComparison
