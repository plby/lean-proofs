import Wikipedia.HopfProblem.HolomorphicPicardNativeCocycle
import Wikipedia.HopfProblem.HolomorphicPicardNativeGluing
import Wikipedia.HopfProblem.HolomorphicPicardNativeRecoveryBasic

/-!
# Gluing the actual native Čech cocycle recovers the original bundle

The cocycle is extracted from the original native charts and then passed
through the general unit-sheaf gluing construction. The resulting native
holomorphic bundle is analytically and fibrewise complex-linearly isomorphic
to the original bundle. The proof does not identify independent choices of
preferred chart indices.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicPicardNative

open HolomorphicCharacterBundle PeriodTorusLineBundleClassificationNative

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
    (M : Type) [TopologicalSpace M] [ChartedSpace H M]
    (V : M → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ω ℂ V I]

/-- Apply the genuine unit-sheaf gluing construction to the actual original
native Čech cocycle. -/
abbrev nativeCocycleData : TransitionData M M :=
  cocycleTransitionData I M (nativeCover M V) (nativeCover_covers M V) (nativeCocycle I M V)

@[simp] theorem nativeCocycleData_baseSet (i : M) :
    (nativeCocycleData I M V).baseSet i = (nativeTriv V i).baseSet := rfl

theorem nativeCocycleData_transition (i j x : M)
    (hx : x ∈ (nativeCocycleData I M V).baseSet i ∩
      (nativeCocycleData I M V).baseSet j) :
    ((nativeCocycleData I M V).transition i j x : ℂ) =
      (scalarTransition V i j x : ℂ) :=
  cocycleTransitionData_transition I M (nativeCover M V)
    (nativeCover_covers M V) (nativeCocycle I M V) i j x hx

/-- For every original native holomorphic complex line bundle, gluing its
actual unit-sheaf cocycle produces an actual analytic bundle isomorphism
back to that original bundle. No presentation or global frame is assumed. -/
def nativeCocycleBundleIso : AnalyticBundleIso I (nativeCocycleData I M V).core.Fiber V :=
  NativeRecovery.analyticBundleIso V (nativeCocycleData I M V)
    (nativeCocycleData_baseSet I M V) (nativeCocycleData_transition I M V) I

/-- Recovery intertwines the actual original local trivializations. -/
theorem nativeCocycleBundleIso_localTriv (i : M) (v : (nativeCocycleData I M V).core.TotalSpace)
    (hv : v.proj ∈ (nativeTriv V i).baseSet) :
    nativeTriv V i ((nativeCocycleBundleIso I M V).diffeomorph v) =
      (nativeCocycleData I M V).core.localTriv i v :=
  NativeRecovery.analyticBundleIso_localTriv V (nativeCocycleData I M V)
    (nativeCocycleData_baseSet I M V) (nativeCocycleData_transition I M V) I i v hv

end Wikipedia.HopfProblem.HolomorphicPicardNative
