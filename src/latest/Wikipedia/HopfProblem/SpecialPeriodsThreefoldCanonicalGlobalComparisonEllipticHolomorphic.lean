import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalComparisonEllipticBasic

/-!
# Holomorphicity of the actual elliptic bundle comparison

The map is proved holomorphic for the original total-space atlases on
the entire order-four patch.  Its preferred scalar need not itself be
holomorphic: in valid native bundle charts the coefficient is the actual
holomorphic elliptic ratio times the original source coefficient.
The same map is also expressed with target the original canonical bundle.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalComparisonElliptic

open TrianglePeriodFamily.Canonical

local notation "IF" => modelWithCornersSelf ℂ Model
local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "Iκ" => ModelWithCorners.prod
  (modelWithCornersSelf ℂ Model) (modelWithCornersSelf ℂ ℂ)

attribute [local instance] Threefold.chartedSpace

local instance ellipticComparisonHolomorphicManifold : IsManifold IF ω Threefold.Space :=
  Threefold.space_isManifold

/-- Only the restriction of the scalar extension to the actual patch is
used; it is the original descended holomorphic ratio there. -/
theorem ratioExtension_holomorphicOn : ContMDiffOn IF I₁ ω ratioExtension patch := by
  have h : ContMDiff IF I₁ ω (fun x : patch => ratioExtension x.val) := by
    have he : (fun x : patch => ratioExtension x.val) =
        GlobalEllipticComparison.patchRatio .four := by
      funext x
      exact ratioExtension_of_mem x.property
    rw [he]
    exact GlobalEllipticComparison.patchRatio_holomorphic .four
  intro x hx
  exact (contMDiffAt_subtype_iff.mp (h ⟨x, hx⟩)).contMDiffWithinAt

theorem ratioExtension_holomorphicAt {x : Threefold.Space} (hx : x ∈ patch) :
    ContMDiffAt IF I₁ ω ratioExtension x :=
  ratioExtension_holomorphicOn.contMDiffAt (patch.isOpen.mem_nhds hx)

/-- Holomorphicity is checked by the actual target local trivialization,
using the matched finite source chart and the proved coefficient identity. -/
theorem totalMap_holomorphicAt (p : sourceBundle.TotalSpace) (hp : p.proj ∈ patch) :
    ContMDiffAt Iκ Iκ ω totalMap p := by
  let i := achart Model p.proj
  have hi : p.proj ∈ i.val.source := mem_chart_source Model p.proj
  have ht : totalMap p ∈ (targetBundle.localTriv i).source := hi
  apply ((targetBundle.localTriv i).contMDiffAt_iff ht).mpr
  have hπ : ContMDiffAt Iκ IF ω (fun q : sourceBundle.TotalSpace => q.proj) p :=
    Bundle.contMDiffAt_proj sourceBundle.Fiber
  refine ⟨hπ, ?_⟩
  have hs : p ∈ (sourceBundle.localTriv (false, some i)).source := source_chart_mem i hp hi
  have he : ContMDiffAt Iκ Iκ ω (sourceBundle.localTriv (false, some i)) p :=
    (sourceBundle.localTriv (false, some i)).contMDiffOn.contMDiffAt
      ((sourceBundle.localTriv (false, some i)).open_source.mem_nhds hs)
  apply (((ratioExtension_holomorphicAt hp).comp p hπ).mul he.snd).congr_of_eventuallyEq
  filter_upwards [hπ.continuousAt (patch.isOpen.mem_nhds hp),
    hπ.continuousAt (i.val.open_source.mem_nhds hi)] with q hq hqi
  exact totalMap_localTriv i q hq hqi

/-- The actual original total-space map is holomorphic over the full
elliptic patch, including the central surface where its section vanishes. -/
theorem totalMap_holomorphicOn :
    ContMDiffOn Iκ Iκ ω totalMap
      (Bundle.TotalSpace.proj ⁻¹' (patch : Set Threefold.Space)) :=
  fun p hp => (totalMap_holomorphicAt p hp).contMDiffWithinAt

/-- The exact interface used to extract native cross-gauge units for
the final global comparison; no local scalar compatibility is assumed. -/
theorem preferredMap_holomorphicOn :
    ContMDiffOn Iκ Iκ ω
      (CanonicalGlobalLineBundle.OpenMaps.preferredMap sourceData targetData preferredUnit)
      (Bundle.TotalSpace.proj ⁻¹' (patch : Set Threefold.Space)) :=
  totalMap_holomorphicOn

theorem chartUnit_holomorphicOn
    (i : GlobalPrescribedDivisor.Index × atlas Model Threefold.Space) :
    ContMDiffOn IF I₁ ω
      (fun x => (CanonicalGlobalLineBundle.OpenMaps.chartUnit
        sourceData targetData preferredUnit i x : ℂ))
      ((sourceData.baseSet i.1 ∩ targetData.baseSet i.2) ∩ (patch : Set Threefold.Space)) :=
  CanonicalGlobalLineBundle.OpenMaps.chartUnit_holomorphicOn
    sourceData targetData preferredUnit IF patch preferredMap_holomorphicOn i

/-- The corresponding map into the unchanged original canonical bundle. -/
def nativeTotalMap (p : sourceBundle.TotalSpace) : Threefold.Canonical.bundle.TotalSpace :=
  NativePresentation.bundleBiholomorph.symm (totalMap p)

/-- The actual fibre comparison with the intrinsic canonical bundle. -/
def nativeFiberEquiv (x : Threefold.Space) :
    sourceBundle.Fiber x ≃L[ℂ] Threefold.Canonical.bundle.Fiber x :=
  (fiberEquiv x).trans (NativePresentation.fiberEquiv x).symm

@[simp] theorem nativeTotalMap_proj (p : sourceBundle.TotalSpace) :
    (nativeTotalMap p).proj = p.proj := rfl

@[simp] theorem nativeTotalMap_mk (x : Threefold.Space) (v : sourceBundle.Fiber x) :
    nativeTotalMap ⟨x, v⟩ = ⟨x, nativeFiberEquiv x v⟩ := rfl

theorem nativeTotalMap_holomorphicOn :
    ContMDiffOn Iκ Iκ ω nativeTotalMap
      (Bundle.TotalSpace.proj ⁻¹' (patch : Set Threefold.Space)) :=
  NativePresentation.bundleBiholomorph.symm.contMDiff.comp_contMDiffOn
    totalMap_holomorphicOn

theorem nativeTotalMap_add (x : Threefold.Space) (v w : sourceBundle.Fiber x) :
    id (α := ℂ) (nativeTotalMap ⟨x, v + w⟩).2 =
      id (α := ℂ) (nativeTotalMap ⟨x, v⟩).2 + id (α := ℂ) (nativeTotalMap ⟨x, w⟩).2 :=
  (nativeFiberEquiv x).map_add v w

theorem nativeTotalMap_smul (x : Threefold.Space) (c : ℂ) (v : sourceBundle.Fiber x) :
    id (α := ℂ) (nativeTotalMap ⟨x, c • v⟩).2 =
      c • id (α := ℂ) (nativeTotalMap ⟨x, v⟩).2 :=
  (nativeFiberEquiv x).map_smul c v

theorem nativeFiberEquiv_ne_zero_iff (x : Threefold.Space) (v : sourceBundle.Fiber x) :
    nativeFiberEquiv x v ≠ 0 ↔ v ≠ 0 := by
  constructor
  · intro h hv
    apply h
    rw [hv, map_zero]
  · intro h hv
    apply h
    apply (nativeFiberEquiv x).injective
    simpa only [map_zero] using hv

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalComparisonElliptic
