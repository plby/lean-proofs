import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTopologicalCoverData
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationNativeIdentification

/-!
# The convex-cover cocycle represents the original native bundle

Restricting the native trivializing cover to balls does not change the bundle.
The scalar-coordinate map gives an actual analytic fibre-linear identification,
checked in both original atlases. No topology or atlas of the native bundle is
replaced by definition.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTopological

open PeriodTorusLineBundleClassificationNative

variable (V : ComplexPlane₂ → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]

def ballFiberIdentification (x : ComplexPlane₂) : (ballData V).core.Fiber x ≃ₗ[ℂ] V x :=
  fiberIdentification V x

def ballToNative (v : (ballData V).core.TotalSpace) : TotalSpace ℂ V :=
  ⟨v.proj, ballFiberIdentification V v.proj v.2⟩

def ballFromNative (v : TotalSpace ℂ V) : (ballData V).core.TotalSpace :=
  ⟨v.proj, (ballFiberIdentification V v.proj).symm v.2⟩

@[simp] theorem ballToNative_proj (v : (ballData V).core.TotalSpace) :
    (ballToNative V v).proj = v.proj := rfl

@[simp] theorem ballFromNative_proj (v : TotalSpace ℂ V) :
    (ballFromNative V v).proj = v.proj := rfl

@[simp] theorem ballToNative_ballFromNative (v : TotalSpace ℂ V) :
    ballToNative V (ballFromNative V v) = v := by
  cases v with
  | mk x v =>
    exact congrArg (TotalSpace.mk x) ((ballFiberIdentification V x).apply_symm_apply v)

@[simp] theorem ballFromNative_ballToNative (v : (ballData V).core.TotalSpace) :
    ballFromNative V (ballToNative V v) = v := by
  cases v with
  | mk x v =>
    exact congrArg (TotalSpace.mk x) ((ballFiberIdentification V x).symm_apply_apply v)

theorem ballCore_coordChange_eq_native (i j x : ComplexPlane₂) (c : ℂ) :
    (ballData V).core.coordChange i j x c =
      (nativeTriv V i).coordChangeL ℂ (nativeTriv V j) x c :=
  (coordChange_apply V i j x c).symm

/-- The ball-cocycle coordinates agree with the original native coordinates,
even on the larger original trivializing set. -/
theorem ballToNative_localTriv (i : ComplexPlane₂) (v : (ballData V).core.TotalSpace)
    (hv : v.proj ∈ (nativeTriv V i).baseSet) :
    nativeTriv V i (ballToNative V v) = (ballData V).core.localTriv i v := by
  change nativeTriv V i
    ⟨v.proj, (nativeTriv V v.proj).symm v.proj (id (α := ℂ) v.2)⟩ =
      (v.proj, (ballData V).core.coordChange v.proj i v.proj v.2)
  rw [← Trivialization.mk_coordChangeL (R := ℂ) _ _
    ⟨FiberBundle.mem_baseSet_trivializationAt ℂ V v.proj, hv⟩]
  exact congrArg (fun c : ℂ => (v.proj, c))
    (ballCore_coordChange_eq_native V v.proj i v.proj (id (α := ℂ) v.2)).symm

theorem ballFromNative_localTriv (i : ComplexPlane₂) (v : TotalSpace ℂ V)
    (hv : v.proj ∈ (nativeTriv V i).baseSet) :
    (ballData V).core.localTriv i (ballFromNative V v) = nativeTriv V i v := by
  rw [← ballToNative_localTriv V i (ballFromNative V v) hv, ballToNative_ballFromNative]

local notation "I₀" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "I₁" => modelWithCornersSelf ℂ ℂ

variable [ContMDiffVectorBundle ω ℂ V I₀]

theorem ballToNative_holomorphic :
    ContMDiff ((I₀).prod I₁) ((I₀).prod I₁) ω (ballToNative V) := by
  intro v
  apply Bundle.contMDiffAt_totalSpace.mpr
  constructor
  · exact Bundle.contMDiffAt_proj (ballData V).core.Fiber
  · change ContMDiffAt ((I₀).prod I₁) I₁ ω
      (fun w => (nativeTriv V v.proj (ballToNative V w)).2) v
    let e := (ballData V).core.localTriv v.proj
    have hv : v ∈ e.source := (ballData V).mem_baseSet_at v.proj
    have he : ContMDiffAt ((I₀).prod I₁) ((I₀).prod I₁) ω e v :=
      e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds hv)
    apply he.snd.congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hv] with w hw
    exact congrArg Prod.snd
      (ballToNative_localTriv V v.proj w (ball_subset_nativeTriv V v.proj hw))

theorem ballFromNative_holomorphic :
    ContMDiff ((I₀).prod I₁) ((I₀).prod I₁) ω (ballFromNative V) := by
  intro v
  apply Bundle.contMDiffAt_totalSpace.mpr
  constructor
  · exact Bundle.contMDiffAt_proj V
  · change ContMDiffAt ((I₀).prod I₁) I₁ ω
      (fun w => ((ballData V).core.localTriv v.proj (ballFromNative V w)).2) v
    let e := nativeTriv V v.proj
    have hv : v ∈ e.source := FiberBundle.mem_trivializationAt_proj_source
    have he : ContMDiffAt ((I₀).prod I₁) ((I₀).prod I₁) ω e v :=
      e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds hv)
    apply he.snd.congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hv] with w hw
    exact congrArg Prod.snd
      (ballFromNative_localTriv V v.proj w (e.mem_source.mp hw))

/-- An actual analytic fibre-linear isomorphism with the ball-refined cocycle
bundle, keeping the native topology and atlas on the target. -/
def ballIdentification : AnalyticBundleIso I₀ (ballData V).core.Fiber V :=
  AnalyticBundleIso.ofFiberEquiv (ballFiberIdentification V)
    (ballToNative_holomorphic V) (ballFromNative_holomorphic V)

@[simp] theorem ballIdentification_apply (v : (ballData V).core.TotalSpace) :
    (ballIdentification V).diffeomorph v = ballToNative V v := rfl

@[simp] theorem ballIdentification_symm_apply (v : TotalSpace ℂ V) :
    (ballIdentification V).diffeomorph.symm v = ballFromNative V v := rfl

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTopological
