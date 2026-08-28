import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicProjectedCoordinates
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumnSphere

/-!
# Target stereographic coordinates for the projected map

The target is the actual quaternionic unit sphere, with its Euclidean norm.
Near each source-chart center, its inverse target chart reconstructs the
original first column. This transfers differential injectivity to a map
between seven-dimensional real vector spaces.
-/

noncomputable section

open scoped ContDiff Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicBottMatrix QuaternionicColumns

local notation "ℍ" => Quaternion ℝ
local notation "QSpace" => QuaternionSpace 1
local notation "QSphere" => SphereCenteredCoordinates.UnitSphere QSpace

def localColumn (z : UnitSphere) (p : ParameterSpace z) : QSphere :=
  ⟨WithLp.toLp 2 (localProjection z p), mem_sphere_zero_iff_norm.mpr
    ((pairing_self_eq_one_iff_norm _).mp (firstColumnFormula_pairing _ _ _))⟩

theorem contDiff_localColumn_val (z : UnitSphere) {n : ℕ∞ω} :
    ContDiff ℝ n (fun p ↦ (localColumn z p).val) :=
  PiLp.contDiff_toLp.comp (contDiff_localProjection z)

theorem continuous_localColumn (z : UnitSphere) : Continuous (localColumn z) :=
  (contDiff_localColumn_val z (n := 0)).continuous.subtype_mk _

abbrev TargetSpace (z : UnitSphere) := SphereCenteredCoordinates.Tangent (localColumn z 0)

def localCoordinateMap (z : UnitSphere) (p : ParameterSpace z) : TargetSpace z :=
  SphereCenteredCoordinates.chart (localColumn z 0) (localColumn z p)

@[simp] theorem localCoordinateMap_zero (z : UnitSphere) : localCoordinateMap z 0 = 0 :=
  SphereCenteredCoordinates.chart_self (localColumn z 0)

theorem contDiffAt_localCoordinateMap (z : UnitSphere) {n : ℕ∞ω} :
    ContDiffAt ℝ n (localCoordinateMap z) 0 := by
  change ContDiffAt ℝ n (fun p ↦ stereoToFun (-(localColumn z 0).val)
    (localColumn z p).val) 0
  exact (SphereCenteredCoordinates.contDiffAt_stereoToFun (localColumn z 0)).comp 0
    (contDiff_localColumn_val z).contDiffAt

theorem localCoordinateMap_reconstruction (z : UnitSphere) :
    (fun p ↦ SphereCenteredCoordinates.inverse (localColumn z 0) (localCoordinateMap z p))
      =ᶠ[𝓝 0] localColumn z := by
  have hmem : ∀ᶠ p in 𝓝 (0 : ParameterSpace z),
      localColumn z p ∈ (SphereCenteredCoordinates.chart (localColumn z 0)).source :=
    (continuous_localColumn z).continuousAt.eventually
      ((SphereCenteredCoordinates.chart (localColumn z 0)).open_source.mem_nhds
        (SphereCenteredCoordinates.self_mem_chart_source (localColumn z 0)))
  filter_upwards [hmem] with p hp
  exact (SphereCenteredCoordinates.chart (localColumn z 0)).left_inv hp

theorem localCoordinateMap_fderiv_kernel (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn)
    (v : ParameterSpace z) (hv : fderiv ℝ (localCoordinateMap z) 0 v = 0) : v = 0 := by
  have hf := (contDiffAt_localCoordinateMap z (n := 1)).differentiableAt (by decide)
  have hi : HasFDerivAt
      (fun q : TargetSpace z ↦ (SphereCenteredCoordinates.inverse (localColumn z 0) q).val)
      (TargetSpace z).subtypeL (localCoordinateMap z 0) := by
    simpa only [localCoordinateMap_zero] using
      SphereCenteredCoordinates.hasFDerivAt_inverse_val (localColumn z 0)
  have hcomp := hi.comp 0 hf.hasFDerivAt
  have heq : (fun p ↦ (localColumn z p).val) =ᶠ[𝓝 0]
      (fun p ↦ (SphereCenteredCoordinates.inverse (localColumn z 0)
        (localCoordinateMap z p)).val) := by
    filter_upwards [localCoordinateMap_reconstruction z] with p hp
    exact congrArg Subtype.val hp.symm
  have hd := hcomp.congr_of_eventuallyEq heq
  have hzero : fderiv ℝ (fun p ↦ (localColumn z p).val) 0 v = 0 := by
    rw [hd.fderiv]
    change (TargetSpace z).subtypeL (fderiv ℝ (localCoordinateMap z) 0 v) = 0
    rw [hv, map_zero]
  have ho := PiLp.contDiff_ofLp (𝕜 := ℝ) (n := 1)
    (p := 2) (E := fun _ : Fin 2 ↦ ℍ)
  have ho' := ho.differentiable (by decide)
  have hf' := (contDiff_localColumn_val z (n := 1)).differentiable (by decide)
  have hchain := (ho' ((localColumn z 0).val)).hasFDerivAt.comp 0 (hf' 0).hasFDerivAt
  change HasFDerivAt (localProjection z) _ 0 at hchain
  apply localProjection_fderiv_kernel z hz v
  rw [hchain.fderiv]
  change fderiv ℝ WithLp.ofLp (localColumn z 0).val
    (fderiv ℝ (fun p ↦ (localColumn z p).val) 0 v) = 0
  rw [hzero, map_zero]

theorem localCoordinateMap_fderiv_injective (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn) :
    Function.Injective (fderiv ℝ (localCoordinateMap z) 0) := by
  intro v w h
  have he : fderiv ℝ (localCoordinateMap z) 0 (v - w) = 0 := by
    rw [map_sub, h, sub_self]
  exact sub_eq_zero.mp (localCoordinateMap_fderiv_kernel z hz (v - w) he)

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
