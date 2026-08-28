import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticRestriction

/-!
# The actual elliptic base lift and its nonvanishing differential

The inverse normalized elliptic chart, restricted to the original root
neighborhood, is a local biholomorphism also at root zero. Its differential
is therefore invertible everywhere. Restricting the source and target to
the genuine punctured regular domains leaves this differential unchanged,
by the chain rule for the actual open-submanifold inclusions.
-/

noncomputable section

open Function Set Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.EllipticCover

open Elliptic EllipticFilling HolomorphicDifferentialForms

local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- The unchanged inverse elliptic chart on the entire actual root domain. -/
def baseLift (j : Kind) : Root j → ℍ := neighborhoodLift j ∘ Subtype.val

@[simp] theorem baseLift_apply (j : Kind) (z : Root j) :
    baseLift j z = neighborhoodLift j z.val := rfl

@[simp] theorem baseLift_rootZero (j : Kind) :
    baseLift j (rootZero j) = Triangle.ellipticCenter j := by
  simp only [baseLift_apply, rootZero_coe, neighborhoodLift_zero]

theorem baseLift_holomorphic (j : Kind) : ContMDiff I₁ I₁ ω (baseLift j) :=
  (neighborhoodLift_holomorphic j).comp contMDiff_subtype_val

/-- The native open inclusion and original elliptic chart give an actual
local biholomorphism on all of the root neighborhood. -/
theorem baseLift_isLocalDiffeomorph (j : Kind) :
    IsLocalDiffeomorph I₁ I₁ ω (baseLift j) := by
  intro z
  have h : IsLocalDiffeomorphAt I₁ I₁ ω (neighborhoodLift j) z.val :=
    ((Triangle.ellipticNeighborhoodChart j).symm.isLocalDiffeomorph z.val).comp
      (K := I₁) (P := ℍ)
      (isLocalDiffeomorph_subtypeVal I₁ (Triangle.ellipticNeighborhood j)
        ((Triangle.ellipticNeighborhoodChart j).symm z.val))
  exact (isLocalDiffeomorph_subtypeVal I₁ (rootDomain j) z).comp
    (K := I₁) (P := ℍ) h

/-- The genuine native differential, with its inverse from the local
biholomorphism rather than from a substituted ambient coordinate. -/
def baseDerivativeEquiv (j : Kind) (z : Root j) : ℂ ≃L[ℂ] ℂ :=
  (baseLift_isLocalDiffeomorph j z).mfderivToContinuousLinearEquiv (by simp)

@[simp] theorem baseDerivativeEquiv_toContinuousLinearMap (j : Kind) (z : Root j) :
    (baseDerivativeEquiv j z : ℂ →L[ℂ] ℂ) = mfderiv I₁ I₁ (baseLift j) z := rfl

/-- The scalar Jacobian of the actual base lift in the inherited native
one-dimensional tangent coordinates. -/
def baseJacobian (j : Kind) (z : Root j) : ℂ := mfderiv I₁ I₁ (baseLift j) z (1 : ℂ)

@[simp] theorem baseJacobian_eq (j : Kind) (z : Root j) :
    baseJacobian j z = mfderiv I₁ I₁ (baseLift j) z (1 : ℂ) := rfl

theorem baseJacobian_ne_zero (j : Kind) (z : Root j) : baseJacobian j z ≠ 0 := by
  intro h
  change baseDerivativeEquiv j z (1 : ℂ) = 0 at h
  exact one_ne_zero ((baseDerivativeEquiv j z).injective
    (h.trans (map_zero (baseDerivativeEquiv j z)).symm))

/-- On the puncture, the regular base map is the same original base lift,
with only the open regular-locus codomain restriction added. -/
@[simp] theorem regularBase_coe_eq_baseLift (j : Kind) (z : RootStar j) :
    (regularBase j z : ℍ) = baseLift j z.val := rfl

/-- Both native open-submanifold inclusions have identity differential;
their actual commuting square identifies the two base differentials. -/
theorem mfderiv_regularBase_eq_baseLift (j : Kind) (z : RootStar j) :
    mfderiv I₁ I₁ (regularBase j) z = mfderiv I₁ I₁ (baseLift j) z.val := by
  let Lr : ℂ →L[ℂ] ℂ := mfderiv I₁ I₁ (regularBase j) z
  let Lb : ℂ →L[ℂ] ℂ := mfderiv I₁ I₁ (baseLift j) z.val
  have hr : HasMFDerivAt I₁ I₁ (regularBase j) z Lr :=
    ((regularBase_holomorphic j z).mdifferentiableAt (by simp)).hasMFDerivAt
  have hb : HasMFDerivAt I₁ I₁ (baseLift j) z.val Lb :=
    ((baseLift_holomorphic j z.val).mdifferentiableAt (by simp)).hasMFDerivAt
  have hregular := (hasMFDerivAt_openSubtypeVal triangleRegularDomain (regularBase j z)).comp
    z hr
  have hroot := hb.comp z (hasMFDerivAt_openSubtypeVal (rootStarDomain j) z)
  have he : (ContinuousLinearMap.id ℂ ℂ).comp Lr =
      Lb.comp (ContinuousLinearMap.id ℂ ℂ) :=
    hregular.mfderiv.symm.trans hroot.mfderiv
  change Lr = Lb
  simpa only [ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id] using he

theorem mfderiv_regularBase_one (j : Kind) (z : RootStar j) :
    mfderiv I₁ I₁ (regularBase j) z (1 : ℂ) = baseJacobian j z.val := by
  exact congrArg (fun L : ℂ →L[ℂ] ℂ => L 1) (mfderiv_regularBase_eq_baseLift j z)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.EllipticCover
