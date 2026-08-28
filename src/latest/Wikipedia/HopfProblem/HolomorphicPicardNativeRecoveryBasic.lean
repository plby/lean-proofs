import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationNativeIso
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationNativeData

/-!
# Recovering an original native bundle from its transition functions

The glued core may select a different preferred chart at each point from the
original native bundle. The fibre map uses that selected original chart, and
the transition identities prove that its expression in every original chart
agrees with the corresponding core chart. Both total-space maps are analytic
for the original native topology and atlas.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicPicardNative.NativeRecovery

open HolomorphicCharacterBundle PeriodTorusLineBundleClassificationNative

variable {M : Type*} [TopologicalSpace M] (V : M → Type*)
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V]
    (A : TransitionData M M)
    (hbase : ∀ i, A.baseSet i = (nativeTriv V i).baseSet)

include hbase in
theorem selected_mem (x : M) : x ∈ (nativeTriv V (A.indexAt x)).baseSet :=
  hbase (A.indexAt x) ▸ A.mem_baseSet_at x

variable [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)] [VectorBundle ℂ ℂ V]

/-- The preferred scalar coordinate is interpreted in the actual selected
native chart, not in an assumed equal preferred native chart. -/
def fiberEquiv (x : M) : A.core.Fiber x ≃ₗ[ℂ] V x :=
  ((nativeTriv V (A.indexAt x)).linearEquivAt ℂ x
    (selected_mem V A hbase x)).symm

def toNative (v : A.core.TotalSpace) : TotalSpace ℂ V :=
  ⟨v.proj, fiberEquiv V A hbase v.proj v.2⟩

def fromNative (v : TotalSpace ℂ V) : A.core.TotalSpace :=
  ⟨v.proj, (fiberEquiv V A hbase v.proj).symm v.2⟩

@[simp] theorem toNative_proj (v : A.core.TotalSpace) :
    (toNative V A hbase v).proj = v.proj := rfl

@[simp] theorem fromNative_proj (v : TotalSpace ℂ V) :
    (fromNative V A hbase v).proj = v.proj := rfl

@[simp] theorem toNative_fromNative (v : TotalSpace ℂ V) :
    toNative V A hbase (fromNative V A hbase v) = v := by
  cases v with
  | mk x v =>
    exact congrArg (TotalSpace.mk x) ((fiberEquiv V A hbase x).apply_symm_apply v)

@[simp] theorem fromNative_toNative (v : A.core.TotalSpace) :
    fromNative V A hbase (toNative V A hbase v) = v := by
  cases v with
  | mk x v =>
    exact congrArg (TotalSpace.mk x) ((fiberEquiv V A hbase x).symm_apply_apply v)

variable (htrans : ∀ i j x, x ∈ A.baseSet i ∩ A.baseSet j →
    (A.transition i j x : ℂ) = (scalarTransition V i j x : ℂ))

include htrans in
theorem coordChange_eq_native (i j x : M) (hx : x ∈ A.baseSet i ∩ A.baseSet j)
    (c : ℂ) :
    A.core.coordChange i j x c = (nativeTriv V i).coordChangeL ℂ (nativeTriv V j) x c := by
  rw [A.core_coordChange_apply, htrans i j x hx]
  exact (coordChange_apply V i j x c).symm

include htrans in
/-- Coordinate compatibility holds on every original chart, independently
of the core's choices of preferred charts. -/
theorem toNative_localTriv (i : M) (v : A.core.TotalSpace)
    (hv : v.proj ∈ (nativeTriv V i).baseSet) :
    nativeTriv V i (toNative V A hbase v) = A.core.localTriv i v := by
  change nativeTriv V i
    ⟨v.proj, (nativeTriv V (A.indexAt v.proj)).symm v.proj (id (α := ℂ) v.2)⟩ =
      (v.proj, A.core.coordChange (A.indexAt v.proj) i v.proj v.2)
  rw [← Trivialization.mk_coordChangeL (R := ℂ) _ _
    ⟨selected_mem V A hbase v.proj, hv⟩]
  exact congrArg (fun c : ℂ => (v.proj, c))
    (coordChange_eq_native V A htrans (A.indexAt v.proj) i v.proj
      ⟨A.mem_baseSet_at v.proj, (hbase i).symm ▸ hv⟩ (id (α := ℂ) v.2)).symm

include htrans in
theorem fromNative_localTriv (i : M) (v : TotalSpace ℂ V)
    (hv : v.proj ∈ (nativeTriv V i).baseSet) :
    A.core.localTriv i (fromNative V A hbase v) = nativeTriv V i v := by
  rw [← toNative_localTriv V A hbase htrans i (fromNative V A hbase v) hv,
    toNative_fromNative]

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] [ChartedSpace H M] (I : ModelWithCorners ℂ E H)
    [ContMDiffVectorBundle ω ℂ V I] [A.IsHolomorphic I]

local notation "I₁" => modelWithCornersSelf ℂ ℂ

omit [ContMDiffVectorBundle ω ℂ V I] in
include htrans in
theorem toNative_holomorphic :
    ContMDiff (I.prod I₁) (I.prod I₁) ω (toNative V A hbase) := by
  intro v
  apply Bundle.contMDiffAt_totalSpace.mpr
  constructor
  · exact Bundle.contMDiffAt_proj A.core.Fiber
  · change ContMDiffAt (I.prod I₁) I₁ ω
      (fun w => (nativeTriv V v.proj (toNative V A hbase w)).2) v
    let e := A.core.localTriv v.proj
    have hv : v ∈ e.source := by
      change v.proj ∈ A.baseSet v.proj
      rw [hbase v.proj]
      exact FiberBundle.mem_baseSet_trivializationAt ℂ V v.proj
    have he : ContMDiffAt (I.prod I₁) (I.prod I₁) ω e v :=
      e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds hv)
    apply he.snd.congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hv] with w hw
    exact congrArg Prod.snd
      (toNative_localTriv V A hbase htrans v.proj w
        (hbase v.proj ▸ (e.mem_source.mp hw : w.proj ∈ A.baseSet v.proj)))

omit [A.IsHolomorphic I] in
include htrans in
theorem fromNative_holomorphic :
    ContMDiff (I.prod I₁) (I.prod I₁) ω (fromNative V A hbase) := by
  intro v
  apply Bundle.contMDiffAt_totalSpace.mpr
  constructor
  · exact Bundle.contMDiffAt_proj V
  · change ContMDiffAt (I.prod I₁) I₁ ω
      (fun w => (A.core.localTriv (A.indexAt v.proj) (fromNative V A hbase w)).2) v
    let e := nativeTriv V (A.indexAt v.proj)
    have hv : v ∈ e.source := e.mem_source.mpr (selected_mem V A hbase v.proj)
    have he : ContMDiffAt (I.prod I₁) (I.prod I₁) ω e v :=
      e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds hv)
    apply he.snd.congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hv] with w hw
    exact congrArg Prod.snd
      (fromNative_localTriv V A hbase htrans (A.indexAt v.proj) w (e.mem_source.mp hw))

/-- A core with the original native transitions on the original cover is
analytically isomorphic to that original native bundle. -/
def analyticBundleIso : AnalyticBundleIso I A.core.Fiber V :=
  AnalyticBundleIso.ofFiberEquiv (fiberEquiv V A hbase)
    (toNative_holomorphic V A hbase htrans I) (fromNative_holomorphic V A hbase htrans I)

@[simp] theorem analyticBundleIso_apply (v : A.core.TotalSpace) :
    (analyticBundleIso V A hbase htrans I).diffeomorph v = toNative V A hbase v := rfl

@[simp] theorem analyticBundleIso_symm_apply (v : TotalSpace ℂ V) :
    (analyticBundleIso V A hbase htrans I).diffeomorph.symm v = fromNative V A hbase v := rfl

theorem analyticBundleIso_localTriv (i : M) (v : A.core.TotalSpace)
    (hv : v.proj ∈ (nativeTriv V i).baseSet) :
    nativeTriv V i ((analyticBundleIso V A hbase htrans I).diffeomorph v) =
      A.core.localTriv i v := toNative_localTriv V A hbase htrans i v hv

end Wikipedia.HopfProblem.HolomorphicPicardNative.NativeRecovery
