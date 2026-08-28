import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalRegularBaseDerivatives
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalRegularTransport

/-!
# The actual affine sphere coordinate on the regular threefold locus

The finite base coordinate agrees literally with the normalized global
sphere projection after the finite complex inclusion.  Its pullback to
the original varying-period family is the invariant function whose
actual native derivative is used in the canonical form.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalRegular

open TrianglePeriodFamily.Canonical

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₃" => modelWithCornersSelf ℂ Model

attribute [local instance] Threefold.chartedSpace specialRegularFamilyChartedSpace
  triangleRegularQuotientChartedSpace

/-- The actual affine coordinate on the native regular torus family. -/
def regularAffineCoordinate (x : Threefold.SpecialRegularFamily) : ℂ :=
  baseCoordinate (specialRegularData.projection x)

theorem regularAffineCoordinate_coe (x : Threefold.SpecialRegularFamily) :
    (regularAffineCoordinate x : RiemannSphere) =
      projectionSphere (regularFamilyInclusion x) :=
  (baseCoordinate_coe (specialRegularData.projection x)).trans
    (regularFamilyInclusion_projectionSphere x).symm

theorem regularAffineCoordinate_holomorphic :
    ContMDiff I₃ I₁ ω regularAffineCoordinate :=
  baseCoordinate_holomorphic.comp (specialRegularData.projection_holomorphic baseCovering)

@[simp] theorem regularAffineCoordinate_familyQuotient (x : SpecialRegularUpstairs) :
    regularAffineCoordinate (familyQuotient x) = upstairsCoordinate x.1 := rfl

/-- The finite affine coordinate of the actual global sphere projection
on its full regular inverse image. -/
def globalAffineCoordinate : regularLocus → ℂ :=
  regularAffineCoordinate ∘ regularLocusBiholomorph

theorem globalAffineCoordinate_coe (y : regularLocus) :
    (globalAffineCoordinate y : RiemannSphere) = projectionSphere y.val :=
  (regularAffineCoordinate_coe (regularLocusBiholomorph y)).trans
    (congrArg projectionSphere (regularLocusBiholomorph_inclusion y))

theorem globalAffineCoordinate_holomorphic :
    ContMDiff I₃ I₁ ω globalAffineCoordinate :=
  regularAffineCoordinate_holomorphic.comp regularLocusBiholomorph.contMDiff

@[simp] theorem globalAffineCoordinate_regularFamily (x : Threefold.SpecialRegularFamily) :
    globalAffineCoordinate (regularFamilyBiholomorph x) = regularAffineCoordinate x :=
  congrArg regularAffineCoordinate (regularFamilyBiholomorph.symm_apply_apply x)

@[simp] theorem globalAffineCoordinate_upstairs (x : SpecialRegularUpstairs) :
    globalAffineCoordinate (regularFamilyBiholomorph (familyQuotient x)) =
      upstairsCoordinate x.1 :=
  (globalAffineCoordinate_regularFamily (familyQuotient x)).trans
    (regularAffineCoordinate_familyQuotient x)

theorem globalAffineCoordinate_ne_zero (y : regularLocus) : globalAffineCoordinate y ≠ 0 :=
  baseCoordinate_ne_zero (specialRegularData.projection (regularLocusBiholomorph y))

theorem globalAffineCoordinate_ne_one (y : regularLocus) : globalAffineCoordinate y ≠ 1 :=
  baseCoordinate_ne_one (specialRegularData.projection (regularLocusBiholomorph y))

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalRegular
