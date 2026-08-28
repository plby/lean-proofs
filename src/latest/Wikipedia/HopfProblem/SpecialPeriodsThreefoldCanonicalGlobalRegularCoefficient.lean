import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalRegularCoordinates
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalGeneratorBasic

/-!
# The actual invariant coefficient `dt/F` on the regular domain

Both factors are the constructed functions: `t` is the finite coordinate
of the actual normalized sphere projection and `F` is the genuine
Eisenstein-root generator for the actual special period.  Their proved
transformation laws cancel the actual full three-dimensional Jacobian.
The coefficient is holomorphic and nowhere zero on the entire regular domain.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalRegular

open TrianglePeriodFamily.Canonical

local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- The actual modular generator restricted to the original regular domain. -/
def regularGenerator (z : TriangleRegularPoint) : ℂ := GlobalGenerator.generator z.val

theorem regularGenerator_holomorphic : ContMDiff I₁ I₁ ω regularGenerator :=
  GlobalGenerator.generator_holomorphic.comp contMDiff_subtype_val

theorem regularGenerator_ne_zero (z : TriangleRegularPoint) : regularGenerator z ≠ 0 :=
  GlobalGenerator.generator_ne_zero_regular z

theorem regularGenerator_generator₁ (z : TriangleRegularPoint) :
    regularGenerator (triangleGenerator₁ • z) =
      specialRegularData.determinantFactor triangleGenerator₁ z * regularGenerator z := by
  change GlobalGenerator.generator (triangleGeometricRepresentation triangleGenerator₁ z.val) = _
  rw [triangleGeometricRepresentation_generator₁_apply, GlobalGenerator.generator_generator₁,
    specialRegularData.determinantFactor_generator₁]
  change -GlobalGenerator.generator z.val / specialTau z.val =
    (-1 / specialTau z.val) * GlobalGenerator.generator z.val
  ring

theorem regularGenerator_generator₂ (z : TriangleRegularPoint) :
    regularGenerator (triangleGenerator₂ • z) =
      specialRegularData.determinantFactor triangleGenerator₂ z * regularGenerator z := by
  change GlobalGenerator.generator (triangleGeometricRepresentation triangleGenerator₂ z.val) = _
  rw [triangleGeometricRepresentation_generator₂_apply, GlobalGenerator.generator_generator₂,
    specialRegularData.determinantFactor_generator₂]
  change GlobalGenerator.generator z.val / specialTau z.val =
    (1 / specialTau z.val) * GlobalGenerator.generator z.val
  ring

/-- The actual generator has the genuine fibre-determinant covariance
under the entire triangle group, not only the two chosen generators. -/
theorem regularGenerator_covariance (g : TriangleGroup) (z : TriangleRegularPoint) :
    regularGenerator (g • z) = specialRegularData.determinantFactor g z * regularGenerator z :=
  determinant_covariant_of_generators regularGenerator regularGenerator_generator₁
    regularGenerator_generator₂ g z

/-- The genuine differential of the global affine coordinate divided
by the actual nonvanishing modular generator. -/
def regularCoefficient (z : TriangleRegularPoint) : ℂ :=
  coordinateDerivative z / regularGenerator z

theorem regularCoefficient_formula (z : TriangleRegularPoint) :
    regularCoefficient z =
      deriv (upstairsCoordinate ∘ (chartAt ℂ z).symm) (z.val : ℂ) /
        GlobalGenerator.generator z.val := rfl

theorem regularCoefficient_holomorphic : ContMDiff I₁ I₁ ω regularCoefficient :=
  coordinateDerivative_holomorphic.div₀ regularGenerator_holomorphic regularGenerator_ne_zero

theorem regularCoefficient_ne_zero (z : TriangleRegularPoint) : regularCoefficient z ≠ 0 :=
  div_ne_zero (coordinateDerivative_ne_zero z) (regularGenerator_ne_zero z)

/-- The coefficient cancels exactly the determinant of the actual
base-and-fibre triangle action in every valid native source chart. -/
theorem regularCoefficient_covariance (g : TriangleGroup) (a z : TriangleRegularPoint)
    (hz : (z.val : ℂ) ∈ (chartAt ℂ a).target) :
    regularCoefficient (g • z) *
      (baseActionDerivative g a z * specialRegularData.determinantFactor g z) =
        regularCoefficient z := by
  unfold regularCoefficient
  rw [regularGenerator_covariance]
  calc
    _ = (coordinateDerivative (g • z) * baseActionDerivative g a z) / regularGenerator z := by
      field_simp [specialRegularData.determinantFactor_ne_zero g z, regularGenerator_ne_zero z]
    _ = _ := congrArg (fun c : ℂ => c / regularGenerator z)
      (coordinateDerivative_action specialRegularData g a z hz)

/-- This is invariance of the genuine ambient canonical-bundle section
under the actual manifold derivative, with every hypothesis discharged. -/
theorem regularCoefficient_invariant : WeightedInvariant regularCoefficient :=
  upstairsWeightedSection_invariant regularCoefficient regularCoefficient_covariance

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalRegular
