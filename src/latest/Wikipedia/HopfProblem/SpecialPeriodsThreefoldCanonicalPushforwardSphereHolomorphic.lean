import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSphereComparison
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Holomorphic comparison with the native sphere cotangent bundle

Both directions are holomorphic in the independently constructed original
bundle atlases.  The derivative cocycle is therefore a genuine presentation
of the native canonical line, not merely a fibrewise algebraic model.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CanonicalGlobal.SphereCanonical

local notation "Iₛ" => ModelWithCorners.prod (modelWithCornersSelf ℂ ℂ)
  (modelWithCornersSelf ℂ ℂ)
local notation "Iᴷ" => ModelWithCorners.prod (modelWithCornersSelf ℂ ℂ)
  (modelWithCornersSelf ℂ (ℂ →L[ℂ] ℂ))

/-- The derivative-cocycle to native cotangent map is genuinely holomorphic. -/
theorem toNative_holomorphic : ContMDiff Iₛ Iᴷ ω toNative := by
  intro q
  let b := data.indexAt q.proj
  have hq : q.proj ∈ data.baseSet b := data.mem_baseSet_at q.proj
  have hsource : toNative q ∈ (cotangentTriv b).source := by
    apply (cotangentTriv b).mem_source.mpr
    rw [cotangentTriv_baseSet]
    exact mem_chartOpen_of_data hq
  apply ((cotangentTriv b).contMDiffAt_iff hsource).mpr
  have hπ : ContMDiffAt Iₛ 𝓘(ℂ) ω
      (fun r : data.core.TotalSpace => r.proj) q :=
    Bundle.contMDiffAt_proj data.core.Fiber
  refine ⟨hπ, ?_⟩
  have he : ContMDiffAt Iₛ Iₛ ω (data.core.localTriv b) q :=
    (data.core.localTriv b).contMDiffOn.contMDiffAt
      ((data.core.localTriv b).open_source.mem_nhds hq)
  have hspan : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (ContinuousLinearMap.toSpanSingletonCLE : ℂ → (ℂ →L[ℂ] ℂ))
      ((data.core.localTriv b q).2) :=
    (ContinuousLinearMap.toSpanSingletonCLE : ℂ ≃L[ℂ] (ℂ →L[ℂ] ℂ)).toContinuousLinearMap.contMDiffAt
  apply (hspan.comp q he.snd).congr_of_eventuallyEq
  filter_upwards [hπ.continuousAt ((data.isOpen_baseSet b).mem_nhds hq)] with r hr
  exact toNative_localTriv b r hr

/-- Reading scalar cotangent coefficients is holomorphic into the original cocycle bundle. -/
theorem fromNative_holomorphic : ContMDiff Iᴷ Iₛ ω fromNative := by
  intro q
  let b := data.indexAt q.proj
  have hq : q.proj ∈ data.baseSet b := data.mem_baseSet_at q.proj
  have hsource : fromNative q ∈ (data.core.localTriv b).source := hq
  apply ((data.core.localTriv b).contMDiffAt_iff hsource).mpr
  have hπ : ContMDiffAt Iᴷ 𝓘(ℂ) ω
      (fun r : CotangentBundle => r.proj) q :=
    Bundle.contMDiffAt_proj CotangentSpace
  refine ⟨hπ, ?_⟩
  apply (cotangentCoefficient_holomorphicAt b (mem_chartOpen_of_data hq)).congr_of_eventuallyEq
  filter_upwards [hπ.continuousAt ((data.isOpen_baseSet b).mem_nhds hq)] with r hr
  exact fromNative_localTriv b r hr

/-- A base-preserving, fibre-linear biholomorphism with the native cotangent total space. -/
def nativeDiffeomorph : Diffeomorph Iₛ Iᴷ data.core.TotalSpace CotangentBundle ω where
  toEquiv := nativeEquiv
  contMDiff_toFun := toNative_holomorphic
  contMDiff_invFun := fromNative_holomorphic

@[simp] theorem nativeDiffeomorph_apply (q : data.core.TotalSpace) :
    nativeDiffeomorph q = toNative q := rfl

@[simp] theorem nativeDiffeomorph_symm_apply (q : CotangentBundle) :
    nativeDiffeomorph.symm q = fromNative q := rfl

@[simp] theorem nativeDiffeomorph_proj (q : data.core.TotalSpace) :
    (nativeDiffeomorph q).proj = q.proj := rfl

@[simp] theorem nativeDiffeomorph_symm_proj (q : CotangentBundle) :
    (nativeDiffeomorph.symm q).proj = q.proj := rfl

/-- The total-space map restricts to the prescribed full cotangent fibre equivalence. -/
theorem nativeDiffeomorph_mk (p : RiemannSphere) (c : data.core.Fiber p) :
    nativeDiffeomorph ⟨p, c⟩ = ⟨p, nativeFiberEquiv p c⟩ := rfl

theorem nativeDiffeomorph_symm_mk (p : RiemannSphere) (α : CotangentSpace p) :
    nativeDiffeomorph.symm ⟨p, α⟩ = ⟨p, (nativeFiberEquiv p).symm α⟩ := rfl

end Wikipedia.HopfProblem.CanonicalGlobal.SphereCanonical
