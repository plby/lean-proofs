import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersCanonical
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersLineBundleGauges
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersComparisonsTensor

/-!
# Squaring the proved genuine canonical-bundle formula

The actual canonical-bundle isomorphism is squared through the native
power functor and then distributed over the actual two tensor factors.
This gives the original canonical square as the tensor of the square
of the pulled-back ideal line and the square of the effective divisor
line, with a genuine holomorphic bundle map and full tensor-fibre
identification.
-/

noncomputable section

open Bundle
open scoped ContDiff TensorProduct

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Powers

open TrianglePeriodFamily.Canonical CanonicalGlobalLineBundle

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

local notation "IF" => modelWithCornersSelf ℂ Model
local notation "Iκ" => ModelWithCorners.prod
  (modelWithCornersSelf ℂ Model) (modelWithCornersSelf ℂ ℂ)

abbrev baseData := GlobalBasePullback.cartier.transitions

abbrev ellipticData := GlobalEllipticDivisor.transitions

/-- The square of the proved original canonical comparison, followed
by the native distribution of tensor powers over the two factors. -/
def squarePrescribedGauge : CrossGauge IF (canonicalData.power 2)
    (tensor (baseData.power 2) (ellipticData.power 2)) :=
  (GlobalComparison.globalGauge.symm.power 2).trans
    (CanonicalGlobalLineBundle.Powers.tensorPowerGauge IF baseData ellipticData 2).toCrossGauge

def squarePrescribedBiholomorph : Diffeomorph Iκ Iκ (bundle 2).TotalSpace
    (tensor (baseData.power 2) (ellipticData.power 2)).core.TotalSpace ω :=
  squarePrescribedGauge.diffeomorph

def squarePrescribedFiberEquiv (x : Threefold.Space) :
    (bundle 2).Fiber x ≃L[ℂ] (tensor (baseData.power 2) (ellipticData.power 2)).core.Fiber x :=
  squarePrescribedGauge.fiberEquiv x

@[simp] theorem squarePrescribedBiholomorph_mk (x : Threefold.Space)
    (v : (bundle 2).Fiber x) :
    squarePrescribedBiholomorph ⟨x, v⟩ = ⟨x, squarePrescribedFiberEquiv x v⟩ := rfl

@[simp] theorem squarePrescribedBiholomorph_proj (p : (bundle 2).TotalSpace) :
    (squarePrescribedBiholomorph p).proj = p.proj := rfl

/-- The fibre comparison reaches the full tensor product of the two
actual squared factor fibres. -/
def prescribedSquareTensorEquiv (x : Threefold.Space) :
    (bundle 2).Fiber x ≃ₗ[ℂ]
      (baseData.power 2).core.Fiber x ⊗[ℂ] (ellipticData.power 2).core.Fiber x :=
  (squarePrescribedFiberEquiv x).toLinearEquiv.trans
    (fibreTensorEquiv (baseData.power 2) (ellipticData.power 2) x).symm

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Powers
