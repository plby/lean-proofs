import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsGroupExtension
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticJacobianFlat
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticRestriction

/-!
# The actual triangle-action Jacobian on the full upper half-plane

The scalar is the native manifold derivative of the original geometric
action, including at every translated elliptic center. It is holomorphic
in the unchanged upper-half-plane atlas and nowhere zero because that
action is a biholomorphism. The identity differentials of the inherited
regular inclusions prove the exact restriction statement.
-/

noncomputable section

open UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.RegularCover

open HolomorphicDifferentialForms

local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- The original full action's derivative in the unit complex base direction. -/
def groupBaseDerivativeExtension (g : TriangleGroup) (z : ℍ) : ℂ :=
  mfderiv I₁ I₁ (triangleGeometricRepresentation g : ℍ → ℍ) z (1 : ℂ)

/-- The actual differential is multiplication by this scalar in the native chart. -/
theorem groupBaseDerivativeExtension_apply (g : TriangleGroup) (z : ℍ) (u : ℂ) :
    mfderiv I₁ I₁ (triangleGeometricRepresentation g : ℍ → ℍ) z u =
      groupBaseDerivativeExtension g z * u := by
  let L : ℂ →L[ℂ] ℂ := mfderiv I₁ I₁ (triangleGeometricRepresentation g : ℍ → ℍ) z
  change L u = L 1 * u
  simpa only [smul_eq_mul, mul_one, mul_comm] using L.map_smul u (1 : ℂ)

theorem groupBaseDerivativeExtension_holomorphic (g : TriangleGroup) :
    ContMDiff I₁ I₁ ω (groupBaseDerivativeExtension g) :=
  FlatDerivative.mfderiv_apply_one_holomorphic_of_constant_charts
    (fun _ _ => rfl) (fun _ _ => rfl)
    (triangleGeometricRepresentation g : ℍ → ℍ)
    (triangleGeometricRepresentation_holomorphic g)

theorem groupBaseDerivativeExtension_ne_zero (g : TriangleGroup) (z : ℍ) :
    groupBaseDerivativeExtension g z ≠ 0 := by
  let L : ℂ ≃L[ℂ] ℂ :=
    (triangleGeometricBiholomorph g).mfderivToContinuousLinearEquiv (by simp) z
  intro h
  change L (1 : ℂ) = 0 at h
  exact one_ne_zero (L.injective (h.trans (map_zero L).symm))

/-- The reciprocal Jacobian is holomorphic also at all elliptic orbit points. -/
theorem groupBaseDerivativeExtension_inv_holomorphic (g : TriangleGroup) :
    ContMDiff I₁ I₁ ω (fun z : ℍ => (groupBaseDerivativeExtension g z)⁻¹) :=
  (groupBaseDerivativeExtension_holomorphic g).inv₀ (groupBaseDerivativeExtension_ne_zero g)

/-- The native differentials commute with both actual regular open inclusions. -/
theorem groupBase_mfderiv_restrict (g : TriangleGroup) (z : TriangleRegularPoint) :
    mfderiv I₁ I₁ (triangleGeometricRepresentation g : ℍ → ℍ) z.val =
      mfderiv I₁ I₁ (fun w : TriangleRegularPoint => g • w) z := by
  let Lr : ℂ →L[ℂ] ℂ := mfderiv I₁ I₁ (fun w : TriangleRegularPoint => g • w) z
  let Lb : ℂ →L[ℂ] ℂ := mfderiv I₁ I₁ (triangleGeometricRepresentation g : ℍ → ℍ) z.val
  have hr : HasMFDerivAt I₁ I₁ (fun w : TriangleRegularPoint => g • w) z Lr :=
    ((triangleRegularAction_holomorphic g z).mdifferentiableAt (by simp)).hasMFDerivAt
  have hb : HasMFDerivAt I₁ I₁ (triangleGeometricRepresentation g : ℍ → ℍ) z.val Lb :=
    ((triangleGeometricRepresentation_holomorphic g z.val).mdifferentiableAt
      (by simp)).hasMFDerivAt
  have hregular := (hasMFDerivAt_openSubtypeVal triangleRegularDomain (g • z)).comp z hr
  have hfull := hb.comp z (hasMFDerivAt_openSubtypeVal triangleRegularDomain z)
  have he : (ContinuousLinearMap.id ℂ ℂ).comp Lr =
      Lb.comp (ContinuousLinearMap.id ℂ ℂ) :=
    hregular.mfderiv.symm.trans hfull.mfderiv
  change Lb = Lr
  simpa only [ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id] using he.symm

/-- Restriction is exactly the original regular-cover scalar Jacobian. -/
@[simp] theorem groupBaseDerivativeExtension_restrict (g : TriangleGroup)
    (z : TriangleRegularPoint) :
    groupBaseDerivativeExtension g z.val = groupBaseDerivative g z :=
  congrArg (fun L : ℂ →L[ℂ] ℂ => L 1) (groupBase_mfderiv_restrict g z)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.RegularCover
