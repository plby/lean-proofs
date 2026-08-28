import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicVectorFieldsClassificationBase
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicVectorFieldsClassificationLift
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicVectorFieldsVertical
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsPeriods
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsGroupAction
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsGroupDerivative
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsGroupTriangular
import Wikipedia.HopfProblem.HolomorphicDifferentialFormsPeriodLaws
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicFormsPeriodic

/-!
# Native vertical coefficients on the actual regular period cover

Every coefficient comes from the inverse differential of the original
cover applied to a genuine global field. Actual verticality removes its
base component. The proved period deck maps then make its entire fibre
restrictions periodic, so compact-lattice Liouville gives fibre
independence. The original triangle lifts give the actual column-vector
covariance, including the lower triangular shear.
-/

noncomputable section

open Matrix
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicVectorFields.Classification

open HolomorphicForms.RegularCover
open HolomorphicDifferentialForms.PeriodLaws
open HolomorphicDifferentialForms.Coordinates.EllipticShear

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  HolomorphicForms.RegularCover.coverChartedSpace HolomorphicForms.RegularCover.cover_isManifold

/-- Actual global verticality kills the original regular base component. -/
theorem regularCoefficients_base (v : Threefold.HolomorphicVectorFields.Field) (x : Cover) :
    (regularCoefficients v x).1 = 0 := by
  apply baseComponent_eq_zero_of_projection x (regularCoefficients v x)
  change mfderiv IF 𝓘(ℂ) Threefold.projectionSphere (globalCover x)
    (mfderiv IF IF globalCover x (regularLift v x)) = 0
  rw [regularLift_map]
  exact projection_mfderiv_apply_eq_zero v (globalCover x)

/-- Deck covariance follows from the actual chain rule and inverse differential. -/
theorem regularCoefficients_deck (v : Threefold.HolomorphicVectorFields.Field)
    (g : Cover → Cover) (hg : ContMDiff IF IF ω g)
    (hcover : ∀ x, globalCover (g x) = globalCover x) (x : Cover) :
    regularCoefficients v (g x) = mfderiv IF IF g x (regularCoefficients v x) :=
  (pullback_covariant globalCover globalCover_isLocalDiffeomorph v g hg hcover x).symm

theorem regularCoefficients_periodic (v : Threefold.HolomorphicVectorFields.Field)
    (z : TriangleRegularPoint) (ℓ : Lattice) (ζ : ComplexPlane₂) :
    regularCoefficients v (z, ζ + PeriodFamilyHolomorphicForms.periodShift data.periods z ℓ) =
      regularCoefficients v (z, ζ) := by
  have h := regularCoefficients_deck v (periodTranslation data.periods ℓ)
    (periodTranslation_holomorphic data.periods ℓ)
    (fun x => globalCover_add_period x.1 ℓ x.2) (z, ζ)
  rw [periodTranslation_apply, mfderiv_periodTranslation] at h
  refine h.trans ?_
  change ((regularCoefficients v (z, ζ)).1,
    (regularCoefficients v (z, ζ)).2 + (regularCoefficients v (z, ζ)).1 •
      PeriodFamilyHolomorphicForms.periodDerivative data.periods z ℓ) =
    regularCoefficients v (z, ζ)
  rw [regularCoefficients_base, zero_smul, add_zero]
  exact Prod.ext (regularCoefficients_base v (z, ζ)).symm rfl

/-- The two original fibre components evaluated at the zero fibre vector. -/
def regularVertical (v : Threefold.HolomorphicVectorFields.Field)
    (z : TriangleRegularPoint) : ComplexPlane₂ := (regularCoefficients v (z, 0)).2

theorem regularVertical_holomorphic (v : Threefold.HolomorphicVectorFields.Field) :
    ContMDiff 𝓘(ℂ) I₂ ω (regularVertical v) :=
  (ContinuousLinearMap.snd ℂ ℂ ComplexPlane₂).contMDiff.comp
    (PeriodFamilyHolomorphicForms.baseCoefficient_holomorphic
      (regularCoefficients_holomorphic v))

/-- The full genuine vector coefficient is vertical and independent of
the original covering-fibre coordinate. No periodicity premise remains. -/
theorem regularCoefficients_eq (v : Threefold.HolomorphicVectorFields.Field)
    (z : TriangleRegularPoint) (ζ : ComplexPlane₂) :
    regularCoefficients v (z, ζ) = (0, regularVertical v z) := by
  have hp : ∀ b ℓ ζ,
      regularCoefficients v (b, ζ + (data.periods.point b).periodVector ℓ) =
        regularCoefficients v (b, ζ) := by
    intro b ℓ ζ
    rw [← PeriodFamilyHolomorphicForms.periodShift_eq_periodVector]
    exact regularCoefficients_periodic v b ℓ ζ
  have h := PeriodFamilyHolomorphicForms.fibre_constant_of_periodic data.periods.point
    (regularCoefficients_holomorphic v) hp z ζ
  exact h.trans (Prod.ext (regularCoefficients_base v (z, 0)) rfl)

/-- The original all-word triangle action gives the actual column-vector law. -/
theorem regularVertical_group (v : Threefold.HolomorphicVectorFields.Field)
    (g : TriangleGroup) (z : TriangleRegularPoint) :
    regularVertical v (g • z) = data.rightBlock g z *ᵥ regularVertical v z := by
  have h := regularCoefficients_deck v (data.complexLift g) (data.complexLift_holomorphic g)
    (globalCover_complexLift g) (z, 0)
  rw [complexLift_mfderiv_apply] at h
  have hs := congrArg Prod.snd h
  simpa only [TrianglePeriodFamily.Data.complexLift, regularCoefficients_eq,
    zero_smul, add_zero] using hs

theorem regularVertical_first_group (v : Threefold.HolomorphicVectorFields.Field)
    (g : TriangleGroup) (z : TriangleRegularPoint) :
    regularVertical v (g • z) 0 = (data.rightBlock g z).det * regularVertical v z 0 := by
  have h := congrFun (regularVertical_group v g z) 0
  simpa only [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    data.rightBlock_zero_one, zero_mul, add_zero, groupRightBlock_det_eq_entry] using h

/-- After the first component vanishes, the fixed second column leaves
an actually invariant second coefficient. -/
theorem regularVertical_second_group_of_first_zero (v : Threefold.HolomorphicVectorFields.Field)
    (hzero : ∀ z, regularVertical v z 0 = 0) (g : TriangleGroup) (z : TriangleRegularPoint) :
    regularVertical v (g • z) 1 = regularVertical v z 1 := by
  have h := congrFun (regularVertical_group v g z) 1
  simpa only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hzero,
    data.rightBlock_one_one, mul_zero, one_mul, zero_add] using h

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicVectorFields.Classification
