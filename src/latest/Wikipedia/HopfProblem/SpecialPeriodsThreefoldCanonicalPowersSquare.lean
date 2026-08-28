import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersSquarePrescribed
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersIntrinsic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersElliptic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersBaseCancellation
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersLineBundleSquare
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersPullbackIdentification

/-!
# The genuine canonical square is the pulled-back sphere ideal line

The actual elliptic quartic equation identifies the square of the
effective order-two divisor line with the actual pulled-back point line.
Combining that native comparison with the proved canonical formula and
the genuine dual cancellation gives `K^2 ≃ f* O(-infinity)`.  Squaring
again gives the source's `K^4 ≃ f* O(-2 infinity)` formula.  Every map
is holomorphic for the original native bundle atlases and complex-linear
on the actual fibres; no divisor-degree arithmetic is substituted for
a bundle comparison.
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

/-- The power-cocycle square and the actual paired-cover tensor square
are identified before applying the actual quartic divisor comparison. -/
def ellipticPowerComparison : CrossGauge IF (ellipticData.power 2) PowersBase.pullbackData :=
  (CanonicalGlobalLineBundle.Powers.squareTensorGauge IF ellipticData).trans
    PowersElliptic.comparison

/-- The square of the true canonical bundle is the original pulled-back
ideal line, through the three proved native bundle comparisons. -/
def canonicalSquareGauge : CrossGauge IF (canonicalData.power 2) baseData :=
  (squarePrescribedGauge.trans (ellipticPowerComparison.tensorLeft (baseData.power 2))).trans
    PowersBase.squarePointCancellation

def canonicalSquareBiholomorph : Diffeomorph Iκ Iκ
    (bundle 2).TotalSpace GlobalBasePullback.bundle.TotalSpace ω :=
  canonicalSquareGauge.diffeomorph

def canonicalSquareFiberEquiv (x : Threefold.Space) :
    (bundle 2).Fiber x ≃L[ℂ] GlobalBasePullback.bundle.Fiber x :=
  canonicalSquareGauge.fiberEquiv x

@[simp] theorem canonicalSquareBiholomorph_proj (p : (bundle 2).TotalSpace) :
    (canonicalSquareBiholomorph p).proj = p.proj := rfl

@[simp] theorem canonicalSquareBiholomorph_symm_proj
    (p : GlobalBasePullback.bundle.TotalSpace) :
    (canonicalSquareBiholomorph.symm p).proj = p.proj := rfl

@[simp] theorem canonicalSquareBiholomorph_mk (x : Threefold.Space)
    (v : (bundle 2).Fiber x) :
    canonicalSquareBiholomorph ⟨x, v⟩ = ⟨x, canonicalSquareFiberEquiv x v⟩ := rfl

@[simp] theorem canonicalSquareBiholomorph_symm_mk (x : Threefold.Space)
    (v : GlobalBasePullback.bundle.Fiber x) :
    canonicalSquareBiholomorph.symm ⟨x, v⟩ = ⟨x, (canonicalSquareFiberEquiv x).symm v⟩ := rfl

/-- This is the full tensor square of intrinsic alternating
three-covectors, identified with the actual ideal-line fibre. -/
def canonicalSquareIntrinsicEquiv (x : Threefold.Space) :
    IntrinsicTensorFiber x 2 ≃ₗ[ℂ] GlobalBasePullback.bundle.Fiber x :=
  (intrinsicTensorFiberEquiv x 2).symm.trans (canonicalSquareFiberEquiv x).toLinearEquiv

/-- An unconditional existence statement for the genuine canonical
square formula, preserving the base and the original complex fibres. -/
theorem canonical_square_bundle_formula :
    ∃ e : Diffeomorph Iκ Iκ (bundle 2).TotalSpace GlobalBasePullback.bundle.TotalSpace ω,
      (∀ p, (e p).proj = p.proj) ∧
      ∀ x, ∃ φ : (bundle 2).Fiber x ≃L[ℂ] GlobalBasePullback.bundle.Fiber x,
        ∀ v, e ⟨x, v⟩ = ⟨x, φ v⟩ :=
  ⟨canonicalSquareBiholomorph, canonicalSquareBiholomorph_proj,
    fun x => ⟨canonicalSquareFiberEquiv x, canonicalSquareBiholomorph_mk x⟩⟩

/-- The fourth power is the actual square of the pulled-back ideal
line; `basePower_eq_pullback` identifies it with the true base pullback. -/
def canonicalFourthPowerGauge : CrossGauge IF (canonicalData.power 4) (baseData.power 2) :=
  (CanonicalGlobalLineBundle.Powers.iteratePowerGauge IF canonicalData 2 2).toCrossGauge.symm.trans
    (canonicalSquareGauge.power 2)

def canonicalFourthPowerBiholomorph : Diffeomorph Iκ Iκ
    (bundle 4).TotalSpace (baseData.power 2).core.TotalSpace ω :=
  canonicalFourthPowerGauge.diffeomorph

@[simp] theorem canonicalFourthPowerBiholomorph_proj (p : (bundle 4).TotalSpace) :
    (canonicalFourthPowerBiholomorph p).proj = p.proj := rfl

theorem canonicalFourthPowerBiholomorph_mk (x : Threefold.Space) (v : (bundle 4).Fiber x) :
    canonicalFourthPowerBiholomorph ⟨x, v⟩ =
      ⟨x, canonicalFourthPowerGauge.fiberEquiv x v⟩ := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Powers
