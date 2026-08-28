import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalCuspHolomorphic

/-!
# Holomorphic comparison of the native and global cusp canonical bundles

Every vector in the original cusp canonical bundle is transported by
inverse pullback along the actual derivative of the cusp inclusion.
The resulting fibrewise-linear map of the original bundle total spaces
is holomorphic.  Its local coefficient formula is proved using the
original native canonical trivialization and the exact signed toric form.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Cusp

open ToricCharts CuspGeometry

local notation "E" => CoordinateSpace 3
local notation "I₃" => modelWithCornersSelf ℂ E
local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "I₁" => modelWithCornersSelf ℂ ℂ

attribute [local instance] CuspGeometry.nativeChartedSpace Threefold.chartedSpace

local instance mapNativeManifold : IsManifold I₃ ω LocalSpace := native_isManifold
local instance mapGlobalManifold : IsManifold IF ω Threefold.Space :=
  Threefold.space_isManifold

/-- Coefficient of a native canonical vector in its original holomorphic
global volume trivialization. -/
def nativeVolumeCoordinate (p : nativeBundle.TotalSpace) : ℂ :=
  (nativeVolumeAtlas.globalTrivialization p).2

theorem nativeVolumeCoordinate_holomorphic :
    ContMDiff ((I₃).prod I₁) I₁ ω nativeVolumeCoordinate :=
  contMDiff_snd.comp nativeVolumeAtlas.globalTrivialization.contMDiff

/-- The original native volume is a basis in each original fibre. -/
theorem eq_nativeVolumeCoordinate_smul (x : LocalSpace) (v : nativeBundle.Fiber x) :
    v = nativeVolumeCoordinate ⟨x, v⟩ • nativeVolume x := by
  change id (α := ℂ) v =
    ((nativeVolumeCoefficient x)⁻¹ * id (α := ℂ) v) * nativeVolumeCoefficient x
  rw [mul_right_comm, inv_mul_cancel₀ (nativeVolumeCoefficient_ne_zero x), one_mul]

/-- Inverse derivative pullback on each original canonical fibre. -/
def nativeForwardMap (p : nativeBundle.TotalSpace) : bundle.TotalSpace :=
  ⟨CuspGeometry.inclusion p.proj, (inclusionPullback p.proj).symm p.2⟩

@[simp] theorem nativeForwardMap_proj (p : nativeBundle.TotalSpace) :
    (nativeForwardMap p).proj = CuspGeometry.inclusion p.proj := rfl

@[simp] theorem nativeForwardMap_mk (x : LocalSpace) (v : nativeBundle.Fiber x) :
    nativeForwardMap ⟨x, v⟩ =
      ⟨CuspGeometry.inclusion x, (inclusionPullback x).symm v⟩ := rfl

theorem nativeForwardMap_add (x : LocalSpace) (v w : nativeBundle.Fiber x) :
    (nativeForwardMap ⟨x, v + w⟩).2 =
      (inclusionPullback x).symm v + (inclusionPullback x).symm w :=
  map_add (inclusionPullback x).symm v w

theorem nativeForwardMap_smul (x : LocalSpace) (c : ℂ) (v : nativeBundle.Fiber x) :
    (nativeForwardMap ⟨x, c • v⟩).2 = c • (nativeForwardMap ⟨x, v⟩).2 :=
  map_smul (inclusionPullback x).symm c v

@[simp] theorem nativeForwardMap_volume (x : LocalSpace) :
    nativeForwardMap ⟨x, nativeVolume x⟩ = volumeAlongInclusionSection x := rfl

/-- The comparison is linear with respect to the genuine descended
native form and its already constructed global image. -/
theorem inclusionPushforward_eq_volumeCoordinate (x : LocalSpace)
    (v : nativeBundle.Fiber x) :
    (inclusionPullback x).symm v =
      nativeVolumeCoordinate ⟨x, v⟩ • volumeAlongInclusion x :=
  (congrArg (inclusionPullback x).symm (eq_nativeVolumeCoordinate_smul x v)).trans
    (map_smul (inclusionPullback x).symm _ _)

/-- In a matching glued cusp chart, the image coefficient is the native
volume coefficient times the original holomorphic fibre coordinate. -/
theorem nativeForwardMap_localCoefficient (i : LocalSpace) (p : nativeBundle.TotalSpace)
    (hp : p.proj ∈ (chartAt E i).source) :
    (bundle.localTriv (gluedCuspChart i) (nativeForwardMap p)).2 =
      nativeVolumeCoordinate p * nativeVolumeCoefficient i := by
  let e := (bundle.localTriv (gluedCuspChart i)).continuousLinearEquivAt ℂ
    (CuspGeometry.inclusion p.proj) (inclusion_mem_gluedCuspChart_source i p.proj hp)
  change e ((inclusionPullback p.proj).symm p.2) = _
  calc
    e ((inclusionPullback p.proj).symm p.2) =
        e (nativeVolumeCoordinate p • volumeAlongInclusion p.proj) :=
      congrArg e (inclusionPushforward_eq_volumeCoordinate p.proj p.2)
    _ = nativeVolumeCoordinate p • e (volumeAlongInclusion p.proj) := map_smul e _ _
    _ = nativeVolumeCoordinate p * nativeVolumeCoefficient i :=
      congrArg (fun z : ℂ => nativeVolumeCoordinate p * z)
        (volumeAlongInclusion_localCoefficient i hp)

/-- The original native chart coefficient is computed in the original
global volume trivialization, with the same signed coefficient. -/
theorem native_localCoefficient (i : LocalSpace) (p : nativeBundle.TotalSpace) :
    (nativeBundle.localTriv i p).2 = nativeVolumeCoordinate p * nativeVolumeCoefficient i := by
  change (nativeVolumeCoefficient i / nativeVolumeCoefficient p.proj) * id (α := ℂ) p.2 =
    ((nativeVolumeCoefficient p.proj)⁻¹ * id (α := ℂ) p.2) * nativeVolumeCoefficient i
  ring

/-- Between the original native and global bundle trivializations, the
comparison is exactly the actual base inclusion times the identity on the fibre. -/
theorem nativeForwardMap_localTriv (i : LocalSpace) (p : nativeBundle.TotalSpace)
    (hp : p.proj ∈ (chartAt E i).source) :
    bundle.localTriv (gluedCuspChart i) (nativeForwardMap p) =
      (CuspGeometry.inclusion p.proj, (nativeBundle.localTriv i p).2) := by
  apply Prod.ext
  · rfl
  · exact (nativeForwardMap_localCoefficient i p hp).trans (native_localCoefficient i p).symm

/-- The actual inverse-pullback map of canonical total spaces is holomorphic
for the original native and glued bundle atlases. -/
theorem nativeForwardMap_holomorphic :
    ContMDiff ((I₃).prod I₁) ((IF).prod I₁) ω nativeForwardMap := by
  have hproj : ContMDiff ((I₃).prod I₁) I₃ ω
      (fun p : nativeBundle.TotalSpace => p.proj) := Bundle.contMDiff_proj _
  intro p
  have hp : nativeForwardMap p ∈ (bundle.localTriv (gluedCuspChart p.proj)).source :=
    inclusion_mem_gluedCuspChart_source p.proj p.proj (mem_chart_source E p.proj)
  apply (bundle.localTriv (gluedCuspChart p.proj)).contMDiffAt_iff hp |>.mpr
  refine ⟨(CuspGeometry.inclusion_holomorphic.comp hproj) p, ?_⟩
  have hc : ContMDiff ((I₃).prod I₁) I₁ ω
      (fun q : nativeBundle.TotalSpace =>
        nativeVolumeCoordinate q * nativeVolumeCoefficient p.proj) :=
    nativeVolumeCoordinate_holomorphic.mul contMDiff_const
  apply hc.contMDiffAt.congr_of_eventuallyEq
  have hn : (fun q : nativeBundle.TotalSpace => q.proj) ⁻¹'
      (chartAt E p.proj).source ∈ 𝓝 p :=
    hproj.continuous.continuousAt.preimage_mem_nhds
      ((chartAt E p.proj).open_source.mem_nhds (mem_chart_source E p.proj))
  filter_upwards [hn] with q hq
  exact nativeForwardMap_localCoefficient p.proj q hq

theorem nativeForwardMap_continuous : Continuous nativeForwardMap :=
  nativeForwardMap_holomorphic.continuous

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Cusp
