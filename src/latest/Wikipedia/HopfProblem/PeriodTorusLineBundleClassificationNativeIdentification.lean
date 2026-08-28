import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationNativeIso
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationNativeData

/-!
# Native line bundles are analytically their scalar cocycle bundles

The forward map interprets the core's preferred scalar coordinate in the
original native trivialization. The inverse takes that coordinate. Their
local expressions agree with the original trivializations, so both maps are
analytic for the independently given native bundle topologies and atlases.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationNative

variable {M : Type*} [TopologicalSpace M] (V : M → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]

/-- Interpret a scalar coordinate in the original fibre at the same base point. -/
def fiberIdentification (x : M) : (data V).core.Fiber x ≃ₗ[ℂ] V x :=
  ((nativeTriv V x).linearEquivAt ℂ x
    (FiberBundle.mem_baseSet_trivializationAt ℂ V x)).symm

/-- The total-space map into the independently given original native bundle. -/
def toNative (v : (data V).core.TotalSpace) : TotalSpace ℂ V :=
  ⟨v.proj, fiberIdentification V v.proj v.2⟩

/-- Take the scalar coordinate of an actual native bundle vector. -/
def fromNative (v : TotalSpace ℂ V) : (data V).core.TotalSpace :=
  ⟨v.proj, (fiberIdentification V v.proj).symm v.2⟩

@[simp] theorem toNative_proj (v : (data V).core.TotalSpace) :
    (toNative V v).proj = v.proj := rfl

@[simp] theorem fromNative_proj (v : TotalSpace ℂ V) :
    (fromNative V v).proj = v.proj := rfl

@[simp] theorem toNative_fromNative (v : TotalSpace ℂ V) :
    toNative V (fromNative V v) = v := by
  cases v with
  | mk x v =>
    exact congrArg (TotalSpace.mk x) ((fiberIdentification V x).apply_symm_apply v)

@[simp] theorem fromNative_toNative (v : (data V).core.TotalSpace) :
    fromNative V (toNative V v) = v := by
  cases v with
  | mk x v =>
    exact congrArg (TotalSpace.mk x) ((fiberIdentification V x).symm_apply_apply v)

/-- The core and native local coordinates literally coincide on each member
of the original native trivializing cover. -/
theorem toNative_localTriv (i : M) (v : (data V).core.TotalSpace)
    (hv : v.proj ∈ (nativeTriv V i).baseSet) :
    nativeTriv V i (toNative V v) = (data V).core.localTriv i v := by
  change nativeTriv V i
    ⟨v.proj, (nativeTriv V v.proj).symm v.proj (id (α := ℂ) v.2)⟩ =
      (v.proj, (data V).core.coordChange v.proj i v.proj v.2)
  rw [← Trivialization.mk_coordChangeL (R := ℂ) _ _
    ⟨FiberBundle.mem_baseSet_trivializationAt ℂ V v.proj, hv⟩]
  exact congrArg (fun c : ℂ => (v.proj, c))
    (core_coordChange_eq_native V v.proj i v.proj (id (α := ℂ) v.2)).symm

theorem fromNative_localTriv (i : M) (v : TotalSpace ℂ V)
    (hv : v.proj ∈ (nativeTriv V i).baseSet) :
    (data V).core.localTriv i (fromNative V v) = nativeTriv V i v := by
  rw [← toNative_localTriv V i (fromNative V v) hv, toNative_fromNative]

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] [ChartedSpace H M] (I : ModelWithCorners ℂ E H)
    [ContMDiffVectorBundle ω ℂ V I]

local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- Analyticity is checked in the original native bundle charts. -/
theorem toNative_holomorphic :
    ContMDiff (I.prod I₁) (I.prod I₁) ω (toNative V) := by
  intro v
  apply Bundle.contMDiffAt_totalSpace.mpr
  constructor
  · exact Bundle.contMDiffAt_proj (data V).core.Fiber
  · change ContMDiffAt (I.prod I₁) I₁ ω
      (fun w => (nativeTriv V v.proj (toNative V w)).2) v
    let e := (data V).core.localTriv v.proj
    have hv : v ∈ e.source := FiberBundle.mem_baseSet_trivializationAt ℂ V v.proj
    have he : ContMDiffAt (I.prod I₁) (I.prod I₁) ω e v :=
      e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds hv)
    apply he.snd.congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hv] with w hw
    exact congrArg Prod.snd (toNative_localTriv V v.proj w hw)

/-- Analyticity of the inverse uses the independently given native charts. -/
theorem fromNative_holomorphic :
    ContMDiff (I.prod I₁) (I.prod I₁) ω (fromNative V) := by
  intro v
  apply Bundle.contMDiffAt_totalSpace.mpr
  constructor
  · exact Bundle.contMDiffAt_proj V
  · change ContMDiffAt (I.prod I₁) I₁ ω
      (fun w => ((data V).core.localTriv v.proj (fromNative V w)).2) v
    let e := nativeTriv V v.proj
    have hv : v ∈ e.source := FiberBundle.mem_trivializationAt_proj_source
    have he : ContMDiffAt (I.prod I₁) (I.prod I₁) ω e v :=
      e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds hv)
    apply he.snd.congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hv] with w hw
    exact congrArg Prod.snd (fromNative_localTriv V v.proj w (e.mem_source.mp hw))

/-- Every native holomorphic complex line bundle is analytically and
fibrewise complex-linearly isomorphic to its extracted scalar cocycle bundle. -/
def identification : AnalyticBundleIso I (data V).core.Fiber V :=
  AnalyticBundleIso.ofFiberEquiv (fiberIdentification V)
    (toNative_holomorphic V I) (fromNative_holomorphic V I)

@[simp] theorem identification_apply (v : (data V).core.TotalSpace) :
    (identification V I).diffeomorph v = toNative V v := rfl

@[simp] theorem identification_symm_apply (v : TotalSpace ℂ V) :
    (identification V I).diffeomorph.symm v = fromNative V v := rfl

@[simp] theorem identification_fiberEquiv (x : M) :
    (identification V I).fiberEquiv x = fiberIdentification V x := rfl

/-- The actual identification intertwines the original local trivializations,
not just the abstract isomorphism classes of the bundles. -/
theorem identification_localTriv (i : M) (v : (data V).core.TotalSpace)
    (hv : v.proj ∈ (nativeTriv V i).baseSet) :
    nativeTriv V i ((identification V I).diffeomorph v) =
      (data V).core.localTriv i v := toNative_localTriv V i v hv

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationNative
