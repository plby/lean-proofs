import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalNativeCanonicalBasic

/-!
# The native canonical bundle and its unit-cocycle presentation are biholomorphic

The original tangent-atlas canonical bundle and the bundle constructed from
its unit-valued reverse-Jacobian transitions carry their own original
total-space topologies and manifold atlases.  The explicit comparison has
identical coefficients in every matched valid trivialization.  Hence both
directions are holomorphic, without transporting either bundle structure.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.NativeCanonical

local notation "I" => modelWithCornersSelf ℂ Model
local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "Iκ" => ModelWithCorners.prod
  (modelWithCornersSelf ℂ Model) (modelWithCornersSelf ℂ ℂ)

variable (M : Type*) [TopologicalSpace M] [ChartedSpace Model M] [IsManifold I ω M]

/-- The native-to-unit-cocycle comparison is holomorphic in the target
bundle's original trivializations. -/
theorem forward_holomorphic : ContMDiff Iκ Iκ ω (forward M) := by
  intro p
  let i := achart Model p.proj
  have hp : p.proj ∈ i.val.source := mem_chart_source Model p.proj
  have htarget : forward M p ∈ ((NativeTransitions.data M).core.localTriv i).source := by
    change (forward M p).proj ∈ i.val.source
    rw [forward_proj]
    exact hp
  apply (((NativeTransitions.data M).core.localTriv i).contMDiffAt_iff
    (f := forward M) (x₀ := p) htarget).mpr
  have hπ : ContMDiffAt Iκ I ω (fun q : (Atlas.core M).TotalSpace => q.proj) p :=
    Bundle.contMDiffAt_proj (Atlas.core M).Fiber
  refine ⟨?_, ?_⟩
  · simpa only [forward_proj] using hπ
  · have he : ContMDiffAt Iκ Iκ ω ((Atlas.core M).localTriv i) p :=
      ((Atlas.core M).localTriv i).contMDiffOn.contMDiffAt
        (((Atlas.core M).localTriv i).open_source.mem_nhds hp)
    apply he.snd.congr_of_eventuallyEq
    filter_upwards [hπ.continuousAt (i.val.open_source.mem_nhds hp)] with q hq
    exact forward_localTriv M i q hq

/-- The explicit inverse is holomorphic for the original tangent-atlas
canonical bundle structure. -/
theorem backward_holomorphic : ContMDiff Iκ Iκ ω (backward M) := by
  intro p
  let i := achart Model p.proj
  have hp : p.proj ∈ i.val.source := mem_chart_source Model p.proj
  have htarget : backward M p ∈ ((Atlas.core M).localTriv i).source := by
    change (backward M p).proj ∈ i.val.source
    rw [backward_proj]
    exact hp
  apply (((Atlas.core M).localTriv i).contMDiffAt_iff
    (f := backward M) (x₀ := p) htarget).mpr
  have hπ : ContMDiffAt Iκ I ω
      (fun q : (NativeTransitions.data M).core.TotalSpace => q.proj) p :=
    Bundle.contMDiffAt_proj (NativeTransitions.data M).core.Fiber
  refine ⟨?_, ?_⟩
  · simpa only [backward_proj] using hπ
  · have he : ContMDiffAt Iκ Iκ ω ((NativeTransitions.data M).core.localTriv i) p :=
      ((NativeTransitions.data M).core.localTriv i).contMDiffOn.contMDiffAt
        (((NativeTransitions.data M).core.localTriv i).open_source.mem_nhds hp)
    apply he.snd.congr_of_eventuallyEq
    filter_upwards [hπ.continuousAt (i.val.open_source.mem_nhds hp)] with q hq
    exact backward_localTriv M i q hq

/-- A genuine biholomorphism between the two original bundle total spaces,
using the explicit native comparison and its literal inverse. -/
def bundleBiholomorph :
    Diffeomorph Iκ Iκ (Atlas.core M).TotalSpace
      (NativeTransitions.data M).core.TotalSpace ω where
  toFun := forward M
  invFun := backward M
  left_inv := backward_forward M
  right_inv := forward_backward M
  contMDiff_toFun := forward_holomorphic M
  contMDiff_invFun := backward_holomorphic M

@[simp] theorem bundleBiholomorph_apply (p : (Atlas.core M).TotalSpace) :
    bundleBiholomorph M p = forward M p := rfl

@[simp] theorem bundleBiholomorph_symm_apply
    (p : (NativeTransitions.data M).core.TotalSpace) :
    (bundleBiholomorph M).symm p = backward M p := rfl

@[simp] theorem bundleBiholomorph_proj (p : (Atlas.core M).TotalSpace) :
    (bundleBiholomorph M p).proj = p.proj := forward_proj M p

@[simp] theorem bundleBiholomorph_symm_proj
    (p : (NativeTransitions.data M).core.TotalSpace) :
    ((bundleBiholomorph M).symm p).proj = p.proj := backward_proj M p

/-- The total-space biholomorphism uses the actual comparison of fibres. -/
@[simp] theorem bundleBiholomorph_mk (x : M) (v : (Atlas.core M).Fiber x) :
    bundleBiholomorph M ⟨x, v⟩ = ⟨x, fiberEquiv M x v⟩ := rfl

@[simp] theorem bundleBiholomorph_symm_mk (x : M)
    (v : (NativeTransitions.data M).core.Fiber x) :
    (bundleBiholomorph M).symm ⟨x, v⟩ = ⟨x, (fiberEquiv M x).symm v⟩ := rfl

theorem bundleBiholomorph_add (x : M) (v w : (Atlas.core M).Fiber x) :
    id (α := ℂ) (bundleBiholomorph M ⟨x, v + w⟩).2 =
      id (α := ℂ) (bundleBiholomorph M ⟨x, v⟩).2 +
        id (α := ℂ) (bundleBiholomorph M ⟨x, w⟩).2 :=
  (fiberEquiv M x).map_add v w

theorem bundleBiholomorph_smul (x : M) (c : ℂ) (v : (Atlas.core M).Fiber x) :
    id (α := ℂ) (bundleBiholomorph M ⟨x, c • v⟩).2 =
      c • id (α := ℂ) (bundleBiholomorph M ⟨x, v⟩).2 :=
  (fiberEquiv M x).map_smul c v

/-- Every valid native coefficient is preserved by the biholomorphism. -/
theorem bundleBiholomorph_localTriv (i : atlas Model M) (p : (Atlas.core M).TotalSpace)
    (hp : p.proj ∈ i.val.source) :
    ((NativeTransitions.data M).core.localTriv i (bundleBiholomorph M p)).2 =
      ((Atlas.core M).localTriv i p).2 :=
  forward_localTriv M i p hp

theorem bundleBiholomorph_symm_localTriv (i : atlas Model M)
    (p : (NativeTransitions.data M).core.TotalSpace) (hp : p.proj ∈ i.val.source) :
    ((Atlas.core M).localTriv i ((bundleBiholomorph M).symm p)).2 =
      ((NativeTransitions.data M).core.localTriv i p).2 :=
  backward_localTriv M i p hp

end Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.NativeCanonical
