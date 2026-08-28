import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCuspExtensionGluing
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCuspExtensionGerm
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCuspExtensionRatio
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCuspExtensionPatch

/-!
# The actual holomorphic unit on the entire filled cusp patch

The reciprocal-normalized canonical ratio is holomorphic and nonzero on
the entire punctured native cusp.  Its computed analytic germ agrees
uniformly near the full central fibre. Filling its forced central value
therefore constructs an unconditional nowhere-zero holomorphic function
on the entire original cusp quotient and hence on the full global patch.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCuspExtension

open ToricCharts CuspGeometry

local notation "I₃" => modelWithCornersSelf ℂ (CoordinateSpace 3)
local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "I₁" => modelWithCornersSelf ℂ ℂ

attribute [local instance] CuspGeometry.nativeChartedSpace Threefold.chartedSpace

local instance unitNativeManifold : IsManifold I₃ ω LocalSpace := native_isManifold
local instance unitGlobalManifold : IsManifold IF ω Threefold.Space := Threefold.space_isManifold

/-- Agreement holds on all points of every sufficiently small actual punctured fibre. -/
theorem normalizedRatio_eq_germ_uniform : ∀ᶠ q : ℂ in 𝓝 0,
    ∀ y : puncturedNative, parameter y.val = q → normalizedRatio y = regularizingGerm q := by
  filter_upwards [normalizedFactor_logarithmic_uniform] with q hq
  intro y hy
  obtain ⟨x, rfl⟩ := logPoint_surjective y
  rw [normalizedRatio_logarithmic]
  exact hq x ((parameter_logPoint x).symm.trans hy)

/-- The actual normalized ratio, with its uniquely forced value on the central fibre. -/
def extensionUnit : LocalSpace → ℂ :=
  fillAcrossZero parameter puncturedNative mem_puncturedNative normalizedRatio (regularizingGerm 0)

@[simp] theorem extensionUnit_punctured (y : puncturedNative) :
    extensionUnit y.val = normalizedRatio y :=
  fillAcrossZero_on_open parameter puncturedNative mem_puncturedNative
    normalizedRatio (regularizingGerm 0) y

theorem extensionUnit_central {y : LocalSpace} (hy : parameter y = 0) :
    extensionUnit y = regularizingGerm 0 :=
  fillAcrossZero_of_zero parameter puncturedNative mem_puncturedNative
    normalizedRatio (regularizingGerm 0) hy

/-- Near each point of the full central fibre the extension is the actual analytic base germ. -/
theorem extensionUnit_eventually_eq_germ {y : LocalSpace} (hy : parameter y = 0) :
    extensionUnit =ᶠ[𝓝 y] regularizingGerm ∘ parameter :=
  fillAcrossZero_eventually_eq parameter puncturedNative mem_puncturedNative
    normalizedRatio regularizingGerm parameter_continuous normalizedRatio_eq_germ_uniform hy

/-- Holomorphicity is in the unchanged native cusp atlas, on the whole original quotient. -/
theorem extensionUnit_holomorphic : ContMDiff I₃ I₁ ω extensionUnit :=
  fillAcrossZero_holomorphic parameter puncturedNative mem_puncturedNative
    normalizedRatio regularizingGerm parameter_holomorphic normalizedRatio_holomorphic
    regularizingGerm_analyticAt normalizedRatio_eq_germ_uniform

/-- The full native extension is a genuine holomorphic unit, including every central stratum. -/
theorem extensionUnit_ne_zero (y : LocalSpace) : extensionUnit y ≠ 0 :=
  fillAcrossZero_ne_zero parameter puncturedNative mem_puncturedNative
    normalizedRatio (regularizingGerm 0) normalizedRatio_ne_zero regularizingGerm_zero_ne_zero y

/-- Exact logarithmic pullback on the full original punctured cusp, not just on a smaller disc. -/
theorem extensionUnit_logarithmic (x : HolomorphicForms.Cusp.LogDomain) :
    extensionUnit (HolomorphicForms.Cusp.localLogMap x) =
      GlobalCusp.reciprocalCoordinate
        (Threefold.projectionSphere (HolomorphicForms.Cusp.globalLogMap x)) *
          GlobalCuspPullback.regularToCuspFactor x :=
  (extensionUnit_punctured (logPoint x)).trans (normalizedRatio_logarithmic x)

/-- The same actual unit on the full global cusp neighborhood. -/
def patchUnit (y : FullCuspPatch) : ℂ := extensionUnit (nativePoint y)

theorem patchUnit_holomorphic : ContMDiff IF I₁ ω patchUnit :=
  extensionUnit_holomorphic.comp nativePatchBiholomorph.symm.contMDiff

theorem patchUnit_ne_zero (y : FullCuspPatch) : patchUnit y ≠ 0 :=
  extensionUnit_ne_zero (nativePoint y)

theorem patchUnit_regular (y : FullCuspPatch) (hy : y.val ∈ regularLocus) :
    patchUnit y = normalizedRatio (regularPatchPoint y hy) :=
  extensionUnit_punctured (regularPatchPoint y hy)

theorem patchUnit_central {y : FullCuspPatch} (hy : patchParameter y = 0) :
    patchUnit y = regularizingGerm 0 := extensionUnit_central hy

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCuspExtension
