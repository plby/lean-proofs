import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundleGauge
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationNativeIso

/-!
# The native core isomorphism for unchanged local transitions

Two original transition-data bundles with the same open sets and the same
overlap transitions have a genuine analytic fibre-linear isomorphism.
Their preferred chart selectors need not agree.  The existing native
gauge construction supplies the necessary change between those selectors,
while its coefficient in every common original chart is exactly one.
-/

noncomputable section

open Bundle Set
open scoped ContDiff

namespace Wikipedia.HopfProblem.LineBundleNormalization.CorePullback

open HolomorphicCharacterBundle CanonicalGlobalLineBundle
  PeriodTorusLineBundleClassificationNative

variable {M ι : Type*} [TopologicalSpace M]
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
    [ChartedSpace H M] (I : ModelWithCorners ℂ E H)
    (A B : TransitionData M ι) (hbase : A.baseSet = B.baseSet)
    (htransition : ∀ i j x, x ∈ A.baseSet i ∩ A.baseSet j →
      B.transition i j x = A.transition i j x)

/-- The actual identity local gauge; no equality of preferred charts is required. -/
def sameTransitionGauge : Gauge I A B where
  baseSet_eq := hbase
  value _ _ := 1
  compatible i j x hx := by
    simpa only [mul_one, one_mul] using htransition i j x hx
  holomorphicOn _ := contMDiffOn_const

variable [A.IsHolomorphic I] [B.IsHolomorphic I]

/-- The original native total spaces and their original holomorphic
atlases are identified by the genuine identity local gauge. -/
def sameTransitionIso : AnalyticBundleIso I A.core.Fiber B.core.Fiber where
  diffeomorph := (sameTransitionGauge I A B hbase htransition).diffeomorph
  fiberEquiv x := ((sameTransitionGauge I A B hbase htransition).fiberEquiv x).toLinearEquiv
  map_fiber x v := (sameTransitionGauge I A B hbase htransition).diffeomorph_mk x v

/-- In the independently selected preferred coordinates, the actual
target transition supplies the required fibre multiplier. -/
theorem sameTransitionIso_fiberEquiv_apply (x : M) (v : A.core.Fiber x) :
    (sameTransitionIso I A B hbase htransition).fiberEquiv x v =
      (B.transition (A.indexAt x) (B.indexAt x) x : ℂ) * id (α := ℂ) v := by
  change ((sameTransitionGauge I A B hbase htransition).preferredMultiplier x : ℂ) *
      id (α := ℂ) v = _
  simp only [Gauge.preferredMultiplier, sameTransitionGauge, mul_one]

/-- The isomorphism preserves each original local scalar coordinate. -/
theorem sameTransitionIso_localCoefficient (i : ι) (v : A.core.TotalSpace)
    (hv : v.proj ∈ A.baseSet i) :
    (B.core.localTriv i ((sameTransitionIso I A B hbase htransition).diffeomorph v)).2 =
      (A.core.localTriv i v).2 := by
  change (B.core.localTriv i
    ((sameTransitionGauge I A B hbase htransition).diffeomorph v)).2 = _
  simpa only [sameTransitionGauge, Units.val_one, one_mul] using
    (sameTransitionGauge I A B hbase htransition).diffeomorph_localCoefficient i v hv

end Wikipedia.HopfProblem.LineBundleNormalization.CorePullback
