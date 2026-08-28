import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalFormula
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersLineBundleBasic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersComparisonsNative

/-!
# The native pluricanonical cocycle bundles

These use powers of the actual tangent-canonical transition functions,
with their original native open cover and native bundle structures.
The first power is holomorphically identified with the original
alternating-cotangent canonical bundle, including its original fibre
identification with all continuous alternating three-covectors.
The full tensor-power fibre identifications are supplied by the
companion tensor-fibre construction.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Powers

open TrianglePeriodFamily.Canonical CanonicalGlobalLineBundle

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

local notation "IF" => modelWithCornersSelf ℂ Model
local notation "Iκ" => ModelWithCorners.prod
  (modelWithCornersSelf ℂ Model) (modelWithCornersSelf ℂ ℂ)

/-- The actual scalar presentation of the native tangent-canonical line. -/
abbrev canonicalData := NativePresentation.transitionData

/-- The actual analytic vector-bundle core of the canonical power cocycle. -/
abbrev bundle (n : ℕ) := (canonicalData.power n).core

theorem bundle_holomorphic (n : ℕ) : ContMDiffVectorBundle ω ℂ (bundle n).Fiber IF :=
  inferInstance

theorem bundle_totalSpace_isManifold (n : ℕ) : IsManifold Iκ ω (bundle n).TotalSpace :=
  inferInstance

/-- Sections are genuine holomorphic sections for the native power-bundle
atlas, not independently prescribed local functions or divisor labels. -/
abbrev HolomorphicSections (n : ℕ) := ContMDiffSection IF ℂ ω (bundle n).Fiber

def firstPowerGauge : Gauge IF (canonicalData.power 1) canonicalData where
  baseSet_eq := rfl
  value _ _ := 1
  compatible i j x _ := by
    change canonicalData.transition i j x * 1 = 1 * canonicalData.transition i j x ^ 1
    rw [pow_one, mul_one, one_mul]
  holomorphicOn _ := contMDiffOn_const

/-- The first power is the original native canonical total space,
through actual fibre-linear holomorphic bundle maps in both directions. -/
def firstPowerBiholomorph : Diffeomorph Iκ Iκ
    (bundle 1).TotalSpace Threefold.Canonical.bundle.TotalSpace ω :=
  firstPowerGauge.diffeomorph.trans NativePresentation.bundleBiholomorph.symm

def firstPowerFiberEquiv (x : Threefold.Space) :
    (bundle 1).Fiber x ≃L[ℂ] Threefold.Canonical.bundle.Fiber x :=
  (firstPowerGauge.fiberEquiv x).trans (NativePresentation.fiberEquiv x).symm

@[simp] theorem firstPowerBiholomorph_mk (x : Threefold.Space) (v : (bundle 1).Fiber x) :
    firstPowerBiholomorph ⟨x, v⟩ = ⟨x, firstPowerFiberEquiv x v⟩ := rfl

@[simp] theorem firstPowerBiholomorph_proj (p : (bundle 1).TotalSpace) :
    (firstPowerBiholomorph p).proj = p.proj := rfl

/-- The fibre at the first power is the full intrinsic alternating
cotangent line of the actual tangent space. -/
def firstPowerIntrinsicEquiv (x : Threefold.Space) :
    (bundle 1).Fiber x ≃L[ℂ] Threefold.Canonical.IntrinsicTopCovector x :=
  (firstPowerFiberEquiv x).trans (Threefold.Canonical.intrinsicEquiv x)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Powers
