import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalCuspMap
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalProductLocal
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPullbackTrivializationGeneral

/-!
# The native cusp canonical comparison is locally biholomorphic

In matching actual bundle trivializations the comparison is the native
cusp inclusion times the identity on the scalar fibre.  The actual local
biholomorphism of the native and global base atlases therefore gives a
local biholomorphism of the original canonical bundle total spaces.
-/

noncomputable section

open Bundle Set Topology Filter
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Cusp

open ToricCharts CuspGeometry

local notation "E" => CoordinateSpace 3
local notation "I₃" => modelWithCornersSelf ℂ E
local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "Iₙ" => ModelWithCorners.prod
  (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ ℂ)
local notation "I𝗀" => ModelWithCorners.prod
  (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (modelWithCornersSelf ℂ ℂ)

attribute [local instance] CuspGeometry.nativeChartedSpace Threefold.chartedSpace

local instance localDiffeomorphNativeManifold : IsManifold I₃ ω LocalSpace := native_isManifold
local instance localDiffeomorphGlobalManifold : IsManifold IF ω Threefold.Space :=
  Threefold.space_isManifold

instance nativeLocalTriv_memTrivializationAtlas (i : LocalSpace) :
    MemTrivializationAtlas (nativeBundle.localTriv i) where
  out := ⟨i, rfl⟩

private theorem nativeLocalDiffeomorphAt_congr
    {f g : nativeBundle.TotalSpace → bundle.TotalSpace} {p : nativeBundle.TotalSpace}
    (hf : IsLocalDiffeomorphAt Iₙ I𝗀 ω f p) (hgf : g =ᶠ[𝓝 p] f) :
    IsLocalDiffeomorphAt Iₙ I𝗀 ω g p := by
  obtain ⟨U, hUf, hU, hpU⟩ := mem_nhds_iff.mp hgf
  obtain ⟨Φ, hp, hΦ⟩ := hf
  let Ψ : PartialDiffeomorph Iₙ I𝗀 nativeBundle.TotalSpace bundle.TotalSpace ω :=
    { toPartialEquiv := (Φ.toOpenPartialHomeomorph.restrOpen U hU).toPartialEquiv
      open_source := (Φ.toOpenPartialHomeomorph.restrOpen U hU).open_source
      open_target := (Φ.toOpenPartialHomeomorph.restrOpen U hU).open_target
      contMDiffOn_toFun := Φ.contMDiffOn_toFun.mono inter_subset_left
      contMDiffOn_invFun := Φ.contMDiffOn_invFun.mono inter_subset_left }
  refine ⟨Ψ, ⟨hp, hpU⟩, ?_⟩
  intro q hq
  exact (hUf hq.2).trans (hΦ hq.1)

/-- The map is exactly the actual product of the base inclusion and the
identity on the fibre, conjugated by the original bundle trivializations. -/
theorem nativeForwardMap_eq_localTriv (i : LocalSpace) (p : nativeBundle.TotalSpace)
    (hp : p.proj ∈ (chartAt E i).source) :
    nativeForwardMap p = (bundle.localTriv (gluedCuspChart i)).toOpenPartialHomeomorph.symm
      (CuspGeometry.inclusion (nativeBundle.localTriv i p).1,
        (nativeBundle.localTriv i p).2) := by
  have hq : nativeForwardMap p ∈ (bundle.localTriv (gluedCuspChart i)).source :=
    inclusion_mem_gluedCuspChart_source i p.proj hp
  calc
    nativeForwardMap p =
        (bundle.localTriv (gluedCuspChart i)).toOpenPartialHomeomorph.symm
          (bundle.localTriv (gluedCuspChart i) (nativeForwardMap p)) :=
      ((bundle.localTriv (gluedCuspChart i)).toOpenPartialHomeomorph.left_inv hq).symm
    _ = _ := congrArg (bundle.localTriv (gluedCuspChart i)).toOpenPartialHomeomorph.symm
      (nativeForwardMap_localTriv i p hp)

/-- The comparison of the original native and global canonical bundles
is a genuine local biholomorphism for their different base models. -/
theorem nativeForwardMap_isLocalDiffeomorph :
    IsLocalDiffeomorph Iₙ I𝗀 ω nativeForwardMap := by
  intro p
  let e := nativeBundle.localTriv p.proj
  let e' := bundle.localTriv (gluedCuspChart p.proj)
  have hp : p ∈ e.source := mem_chart_source E p.proj
  have hj : CuspGeometry.inclusion p.proj ∈ e'.baseSet :=
    inclusion_mem_gluedCuspChart_source p.proj p.proj (mem_chart_source E p.proj)
  have hs : IsLocalDiffeomorphAt Iₙ Iₙ ω e p :=
    TrianglePeriodFamily.Canonical.Pullback.trivialization_isLocalDiffeomorphAt
      (I := I₃) e hp
  have hw : IsLocalDiffeomorphAt Iₙ I𝗀 ω
      (fun q : LocalSpace × ℂ => (CuspGeometry.inclusion q.1, q.2)) (e p) :=
    CanonicalProduct.isLocalDiffeomorphAt_prodLine
      (CuspGeometry.inclusion_isLocalDiffeomorph p.proj)
  have ht : IsLocalDiffeomorphAt I𝗀 I𝗀 ω e'.toOpenPartialHomeomorph.symm
      (CuspGeometry.inclusion (e p).1, (e p).2) :=
    TrianglePeriodFamily.Canonical.Pullback.trivialization_symm_isLocalDiffeomorphAt
      (I := IF) e' (e'.mem_target.mpr hj)
  have hfirst := hs.comp (K := I𝗀) (P := Threefold.Space × ℂ) hw
  have hall := hfirst.comp (K := I𝗀) (P := bundle.TotalSpace) ht
  apply nativeLocalDiffeomorphAt_congr hall
  filter_upwards [e.open_source.mem_nhds hp] with q hq
  exact nativeForwardMap_eq_localTriv p.proj q hq

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Cusp
