import Wikipedia.HopfProblem.ThreefoldLineBundleNormalizationCorePullbackGauge
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernPullbackBundleNative

/-!
# Native pullback cores with the original pulled local transitions

The frozen native pullback comparison first identifies Mathlib's actual
pullback topology with the pulled transition-data core.  The genuine
identity local gauge then compares that core with independently constructed
target transition data on the inverse-image cover.  No equality of the
preferred chart selectors or of the native bundle topologies is assumed.
-/

noncomputable section

open Bundle Set
open scoped ContDiff

namespace Wikipedia.HopfProblem.LineBundleNormalization.CorePullback

open HolomorphicCharacterBundle CanonicalGlobalLineBundle
  PeriodTorusLineBundleClassificationNative PeriodTorusLineBundleChernPullback

variable {M N ι : Type*} [TopologicalSpace M] [TopologicalSpace N]
    {E H E' H' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] [TopologicalSpace H']
    [ChartedSpace H M] [ChartedSpace H' N]
    (I : ModelWithCorners ℂ E H) (J : ModelWithCorners ℂ E' H')
    (A : TransitionData M ι) (B : TransitionData N ι)
    (f : ContMDiffMap J I N M ω)
    (hbase : (CanonicalGlobalLineBundle.pullback A f f.contMDiff.continuous).baseSet = B.baseSet)
    (htransition : ∀ i j x,
      x ∈ (CanonicalGlobalLineBundle.pullback A f f.contMDiff.continuous).baseSet i ∩
        (CanonicalGlobalLineBundle.pullback A f f.contMDiff.continuous).baseSet j →
      B.transition i j x = A.transition i j (f x))
    [A.IsHolomorphic I] [B.IsHolomorphic J]

local notation "P" => CanonicalGlobalLineBundle.pullback A f f.contMDiff.continuous

/-- The actual native pullback is analytically isomorphic to an original
core with the pulled local transitions on the original inverse-image cover. -/
def nativeCorePullbackIso : AnalyticBundleIso J ((f : N → M) *ᵖ A.core.Fiber) B.core.Fiber := by
  letI : (P).IsHolomorphic J :=
    CanonicalGlobalLineBundle.pullback_isHolomorphic A f f.contMDiff.continuous J I f.contMDiff
  exact (pullbackNativeIso A J I f).symm.trans
    (sameTransitionIso J P B hbase htransition)

/-- The fibre formula retains the target transition between the
inherited preferred chart and the independently chosen target chart. -/
theorem nativeCorePullbackIso_fiberEquiv_apply (x : N)
    (v : ((f : N → M) *ᵖ A.core.Fiber) x) :
    (nativeCorePullbackIso I J A B f hbase htransition).fiberEquiv x v =
      (B.transition (A.indexAt (f x)) (B.indexAt x) x : ℂ) * id (α := ℂ) v := by
  let : (P).IsHolomorphic J :=
    CanonicalGlobalLineBundle.pullback_isHolomorphic A f f.contMDiff.continuous J I f.contMDiff
  change (sameTransitionIso J P B hbase htransition).fiberEquiv x
      (id (α := ℂ) v) = _
  exact sameTransitionIso_fiberEquiv_apply J P B hbase htransition x (id (α := ℂ) v)

/-- Each original target chart preserves the corresponding original
source scalar coordinate, evaluated on the actual native pullback lift. -/
theorem nativeCorePullbackIso_localCoefficient (i : ι)
    (v : TotalSpace ℂ ((f : N → M) *ᵖ A.core.Fiber))
    (hv : f v.proj ∈ A.baseSet i) :
    (B.core.localTriv i
        ((nativeCorePullbackIso I J A B f hbase htransition).diffeomorph v)).2 =
      (A.core.localTriv i (Bundle.Pullback.lift (f : N → M) v)).2 := by
  let : (P).IsHolomorphic J :=
    CanonicalGlobalLineBundle.pullback_isHolomorphic A f f.contMDiff.continuous J I f.contMDiff
  change (B.core.localTriv i
      ((sameTransitionIso J P B hbase htransition).diffeomorph
        ((pullbackNativeIso A J I f).diffeomorph.symm v))).2 = _
  exact sameTransitionIso_localCoefficient J P B hbase htransition i
    ((pullbackNativeIso A J I f).diffeomorph.symm v) hv

end Wikipedia.HopfProblem.LineBundleNormalization.CorePullback
