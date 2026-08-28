import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalCusp
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalCuspCharts
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPullbackCoordinatesGeneral

/-!
# Holomorphic gluing of the native cusp volume

The actual derivative-pullback comparison gives the signed native volume
coefficient in every matching glued cusp chart.  These coefficients are
constant on each chart.  Consequently the transported form is a
nowhere-zero holomorphic section of the genuine global canonical bundle
over the full cusp patch, including its central fibre.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Cusp

open ToricCharts CuspGeometry

local notation "E" => CoordinateSpace 3
local notation "F" => ℂ × ComplexPlane₂
local notation "I₃" => modelWithCornersSelf ℂ E
local notation "IF" => modelWithCornersSelf ℂ F
local notation "I₁" => modelWithCornersSelf ℂ ℂ

attribute [local instance] CuspGeometry.nativeChartedSpace Threefold.chartedSpace

local instance holomorphicNativeManifold : IsManifold I₃ ω LocalSpace := native_isManifold
local instance holomorphicGlobalManifold : IsManifold IF ω Threefold.Space :=
  Threefold.space_isManifold

/-- In matching native and global cusp charts, the actual differential
commutes with the native-to-product coordinate equivalence. -/
theorem inclusionDerivative_gluedCuspChart (i : LocalSpace) {x : LocalSpace}
    (hx : x ∈ (chartAt E i).source) :
    ((tangentBundleCore IF Threefold.Space).coordChange (gluedCuspChart i)
      (achart F (CuspGeometry.inclusion x)) (CuspGeometry.inclusion x)).comp
        cuspModelEquiv.toContinuousLinearMap =
      (mfderiv I₃ IF CuspGeometry.inclusion x).comp
        ((tangentBundleCore I₃ LocalSpace).coordChange (achart E i) (achart E x) x) := by
  let T := tangentBundleCore IF Threefold.Space
  let p := achart F (CuspGeometry.inclusion x)
  let j := gluedCuspChart i
  have hp : CuspGeometry.inclusion x ∈ T.baseSet p := mem_chart_source F _
  have hj : CuspGeometry.inclusion x ∈ T.baseSet j :=
    inclusion_mem_gluedCuspChart_source i x hx
  have hcoord := TrianglePeriodFamily.Canonical.Pullback.fderiv_coordinates_eq_tangentCore
    CuspGeometry.inclusion (achart E i) j hx hj
      ((inclusion_isLocalDiffeomorph x).mdifferentiableAt (by simp))
  have he : cuspModelEquiv.toContinuousLinearMap =
      (T.coordChange p j (CuspGeometry.inclusion x)).comp
        ((mfderiv I₃ IF CuspGeometry.inclusion x).comp
          ((tangentBundleCore I₃ LocalSpace).coordChange (achart E i) (achart E x) x)) :=
    (gluedCuspChart_inclusion_fderiv i ((chartAt E i).map_source hx)).symm.trans hcoord
  have hcancel : (T.coordChange j p (CuspGeometry.inclusion x)).comp
      (T.coordChange p j (CuspGeometry.inclusion x)) = ContinuousLinearMap.id ℂ F := by
    rw [T.coordChange_linear_comp p j p _ ⟨⟨hp, hj⟩, hp⟩]
    apply ContinuousLinearMap.ext
    intro v
    exact T.coordChange_self p _ hp v
  apply ContinuousLinearMap.ext
  intro v
  exact (congrArg (fun A : E →L[ℂ] F =>
    T.coordChange j p (CuspGeometry.inclusion x) (A v)) he).trans
      (congrArg (fun A : F →L[ℂ] F => A
        ((mfderiv I₃ IF CuspGeometry.inclusion x)
          ((tangentBundleCore I₃ LocalSpace).coordChange (achart E i) (achart E x) x v)))
        hcancel)

/-- The native bundle's signed volume in any chart, expressed through
the actual tangent-coordinate change. -/
theorem nativeVolume_tangentCoordinates (i : LocalSpace) {x : LocalSpace}
    (hx : x ∈ (chartAt E i).source) :
    (nativeIntrinsicEquiv x (nativeVolume x)).compContinuousLinearMap
        ((tangentBundleCore I₃ LocalSpace).coordChange (achart E i) (achart E x) x) =
      nativeVolumeCoefficient i • CanonicalBundle.volume := by
  rw [TrianglePeriodFamily.Canonical.Pullback.tangentBundleCore_coordChange_self]
  calc
    _ = nativeVolumeAtlas.inCoordinates i x (nativeVolume x) :=
      (native_inCoordinates_eq_intrinsic_pullback i hx (nativeVolume x)).symm
    _ = nativeVolumeCoefficient i • CanonicalBundle.volume :=
      nativeVolumeAtlas.volumeSection_inCoordinates i x

/-- The global cusp form has precisely the original signed toric
coefficient in each matching actual glued chart. -/
theorem volumeAlongInclusion_inCoordinates (i : LocalSpace) {x : LocalSpace}
    (hx : x ∈ (chartAt E i).source) :
    inCoordinates (gluedCuspChart i) (CuspGeometry.inclusion x) (volumeAlongInclusion x) =
      nativeVolumeCoefficient i • TrianglePeriodFamily.Canonical.volume := by
  let L := (tangentBundleCore IF Threefold.Space).coordChange (gluedCuspChart i)
    (achart F (CuspGeometry.inclusion x)) (CuspGeometry.inclusion x)
  let S := (tangentBundleCore I₃ LocalSpace).coordChange (achart E i) (achart E x) x
  let α := intrinsicEquiv (CuspGeometry.inclusion x) (volumeAlongInclusion x)
  let eDual : TrianglePeriodFamily.Canonical.TopCovector ≃L[ℂ] CanonicalBundle.TopCovector :=
    cuspModelEquiv.symm.continuousAlternatingMapCongrLeft
  apply eDual.injective
  change (inCoordinates (gluedCuspChart i) (CuspGeometry.inclusion x)
    (volumeAlongInclusion x)).compContinuousLinearMap cuspModelEquiv.toContinuousLinearMap = _
  have hnative : α.compContinuousLinearMap (mfderiv I₃ IF CuspGeometry.inclusion x) =
      nativeIntrinsicEquiv x (nativeVolume x) :=
    (volumeAlongInclusion_pullback x).trans (nativeIntrinsicEquiv_volume x).symm
  calc
    _ = (α.compContinuousLinearMap L).compContinuousLinearMap
        cuspModelEquiv.toContinuousLinearMap :=
      congrArg (fun β : TrianglePeriodFamily.Canonical.TopCovector =>
        β.compContinuousLinearMap cuspModelEquiv.toContinuousLinearMap)
          (inCoordinates_eq_intrinsic_pullback (gluedCuspChart i)
            (CuspGeometry.inclusion x) (volumeAlongInclusion x))
    _ = α.compContinuousLinearMap (L.comp cuspModelEquiv.toContinuousLinearMap) := rfl
    _ = α.compContinuousLinearMap
        ((mfderiv I₃ IF CuspGeometry.inclusion x).comp S) :=
      congrArg (fun A : E →L[ℂ] F => α.compContinuousLinearMap A)
        (inclusionDerivative_gluedCuspChart i hx)
    _ = (α.compContinuousLinearMap (mfderiv I₃ IF CuspGeometry.inclusion x)).compContinuousLinearMap
        S := rfl
    _ = (nativeIntrinsicEquiv x (nativeVolume x)).compContinuousLinearMap S :=
      congrArg (fun β : NativeIntrinsicTopCovector x => β.compContinuousLinearMap S) hnative
    _ = nativeVolumeCoefficient i • CanonicalBundle.volume :=
      nativeVolume_tangentCoordinates i hx
    _ = (nativeVolumeCoefficient i • TrianglePeriodFamily.Canonical.volume).compContinuousLinearMap
        cuspModelEquiv.toContinuousLinearMap := by
      rw [← volume_cuspModelEquiv_pullback]
      rfl

theorem volumeAlongInclusion_localCoefficient (i : LocalSpace) {x : LocalSpace}
    (hx : x ∈ (chartAt E i).source) :
    (bundle.localTriv (gluedCuspChart i)
      ⟨CuspGeometry.inclusion x, volumeAlongInclusion x⟩).2 = nativeVolumeCoefficient i := by
  apply TrianglePeriodFamily.Canonical.coefficientEquiv.injective
  exact volumeAlongInclusion_inCoordinates i hx

/-- The transported toric volume as a map into the actual global bundle. -/
def volumeAlongInclusionSection (x : LocalSpace) : bundle.TotalSpace :=
  ⟨CuspGeometry.inclusion x, volumeAlongInclusion x⟩

/-- Holomorphicity follows from constant signed coefficients in the
actual glued cusp charts and holomorphicity of the actual inclusion. -/
theorem volumeAlongInclusionSection_holomorphic :
    ContMDiff I₃ ((IF).prod I₁) ω volumeAlongInclusionSection := by
  intro x
  have hx : volumeAlongInclusionSection x ∈ (bundle.localTriv (gluedCuspChart x)).source :=
    inclusion_mem_gluedCuspChart_source x x (mem_chart_source E x)
  apply (bundle.localTriv (gluedCuspChart x)).contMDiffAt_iff hx |>.mpr
  refine ⟨CuspGeometry.inclusion_holomorphic x, ?_⟩
  apply (contMDiffAt_const (c := nativeVolumeCoefficient x)).congr_of_eventuallyEq
  filter_upwards [(chartAt E x).open_source.mem_nhds (mem_chart_source E x)] with y hy
  exact volumeAlongInclusion_localCoefficient x hy

theorem patchVolumeSection_eq_transport (y : Threefold.liftedPatch (some none)) :
    patchVolumeSection y = volumeAlongInclusionSection (nativePatchBiholomorph.symm y) := by
  apply Bundle.TotalSpace.ext
    (congrArg Subtype.val (nativePatchBiholomorph.apply_symm_apply y)).symm
  rfl

/-- The native cusp volume glues to a holomorphic section on the entire
actual global cusp patch, including the central cusp fibre. -/
theorem patchVolumeSection_holomorphic :
    ContMDiff IF ((IF).prod I₁) ω patchVolumeSection := by
  have h : patchVolumeSection = volumeAlongInclusionSection ∘ nativePatchBiholomorph.symm :=
    funext patchVolumeSection_eq_transport
  rw [h]
  exact volumeAlongInclusionSection_holomorphic.comp nativePatchBiholomorph.symm.contMDiff

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Cusp
