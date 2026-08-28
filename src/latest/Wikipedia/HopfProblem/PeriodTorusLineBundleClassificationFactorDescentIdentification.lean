import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFactorDescentCoordinates
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# An analytic native bundle isomorphism from an equivariant covering frame

Both directions are proved holomorphic in the original native charts. In
particular, the inverse divides by the actual nowhere-zero frame
coefficient, and its analyticity is not assumed as part of the input.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFactorDescent

open PeriodTorusAppellHumbert PeriodTorusLineBundleClassificationNative

local notation "IC" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "I₁" => modelWithCornersSelf ℂ ℂ

variable {p : PeriodDomain} {V : p.Torus → Type*}
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ω ℂ V IC]

variable (s : CoverSection p V) (hne : ∀ z, s z ≠ 0) (F : FactorOfAutomorphy p)
    (hrel : ∀ (l : p.lattice) (z : ComplexPlane₂) (c : ℂ),
      coverScalarMap s (z + l, (F.factor l z : ℂ) * c) = coverScalarMap s (z, c))

include hrel

theorem frameNativeToCore_contMDiff :
    ContMDiff ((IC).prod I₁) ((IC).prod I₁) ω (frameNativeToCore s hne F) := by
  intro v
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨Bundle.contMDiffAt_proj V, ?_⟩
  change ContMDiffAt ((IC).prod I₁) I₁ ω
    (fun w => ((Core.data F).core.localTriv v.proj (frameNativeToCore s hne F w)).2) v
  let b := v.proj
  let e := nativeTriv V b
  have hv : v ∈ e.source := FiberBundle.mem_trivializationAt_proj_source
  have hb : b ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt ℂ V b
  have hbase : b ∈ Core.baseSet p b := Core.mem_baseSet p b
  have he : ContMDiffAt ((IC).prod I₁) ((IC).prod I₁) ω e v :=
    e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds hv)
  have hl : ContMDiffAt IC IC ω (Core.lift p b) b :=
    (Core.lift_holomorphic p b).contMDiffAt ((Core.isOpen_baseSet p b).mem_nhds hbase)
  have hz : p.lattice.mkQ (Core.lift p b b) ∈ (nativeTriv V b).baseSet := by
    rw [Core.lift_project p b hbase]
    exact hb
  have hc : ContMDiffAt IC I₁ ω (coefficient s b) (Core.lift p b b) :=
    coefficient_contMDiffAt s b (Core.lift p b b) hz
  have hp : ContMDiffAt ((IC).prod I₁) IC ω
      (fun w : TotalSpace ℂ V => w.proj) v := Bundle.contMDiffAt_proj V
  have hLift : ContMDiffAt ((IC).prod I₁) IC ω
      (fun w : TotalSpace ℂ V => Core.lift p b w.proj) v :=
    ContMDiffAt.comp (f := fun w : TotalSpace ℂ V => w.proj)
      (g := Core.lift p b) v hl hp
  have hd : ContMDiffAt ((IC).prod I₁) I₁ ω
      (fun w : TotalSpace ℂ V => coefficient s b (Core.lift p b w.proj)) v :=
    ContMDiffAt.comp (f := fun w : TotalSpace ℂ V => Core.lift p b w.proj)
      (g := coefficient s b) v hc hLift
  have hne' : coefficient s b (Core.lift p b b) ≠ 0 :=
    coefficient_ne_zero s hne b _ hz
  apply (he.snd.mul (hd.inv₀ hne')).congr_of_eventuallyEq
  have hnear : ∀ᶠ w : TotalSpace ℂ V in 𝓝 v, w.proj ∈ Core.baseSet p b :=
    (FiberBundle.continuous_proj ℂ V).continuousAt
      ((Core.isOpen_baseSet p b).mem_nhds hbase)
  filter_upwards [hnear, e.open_source.mem_nhds hv] with w hw hew
  change ((Core.data F).core.localTriv b (frameNativeToCore s hne F w)).2 =
    (nativeTriv V b w).2 * (coefficient s b (Core.lift p b w.proj))⁻¹
  rw [← div_eq_mul_inv]
  exact frameNativeToCore_localTriv s hne F hrel b b w hw (e.mem_source.mp hew)

/-- The actual analytic fibre-linear isomorphism, with the independently
proved analytic inverse on the original native total spaces. -/
def frameDescentIso : AnalyticBundleIso IC (Core.data F).core.Fiber V :=
  AnalyticBundleIso.ofFiberEquiv (frameFiberEquiv s hne F)
    (frameCoreToNative_contMDiff s hne F hrel)
    (frameNativeToCore_contMDiff s hne F hrel)

@[simp]
theorem frameDescentIso_apply (u : (Core.data F).core.TotalSpace) :
    (frameDescentIso s hne F hrel).diffeomorph u = frameCoreToNative s hne F u := rfl

@[simp]
theorem frameDescentIso_symm_apply (v : TotalSpace ℂ V) :
    (frameDescentIso s hne F hrel).diffeomorph.symm v = frameNativeToCore s hne F v := rfl

/-- The isomorphism genuinely sends the orbit representative `[z,c]` to
`c • s(z)` in the original bundle. -/
theorem frameDescentIso_associatedMap (z : ComplexPlane₂) (c : ℂ) :
    (frameDescentIso s hne F hrel).diffeomorph
      (Core.fromAssociated F (associatedMap F (z, c))) = coverScalarMap s (z, c) :=
  frameCoreToNative_fromAssociated s hne F hrel z c

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFactorDescent
