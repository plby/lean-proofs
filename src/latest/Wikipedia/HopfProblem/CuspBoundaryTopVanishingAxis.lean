import Wikipedia.HopfProblem.CuspCentralHomologyRadialAnnulus
import Mathlib.Topology.Homotopy.Contractible

/-!
# An explicit ambient nullhomotopy of the annular axis

The part of the literal radial annulus on the first coordinate axis
contracts inside the annulus, not inside that disconnected axis.  Its
direction is moved toward `(0, 1/2)` by affine interpolation, which never
meets zero.  The gauge radius is interpolated within the open annular
range, and rescaling the direction realizes that radius exactly.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspBoundaryTopVanishing

open CuspCentralHomology.Radial

local notation "Plane" => CuspHoneycombTiling.Plane

/-- The actual first-coordinate axis in the literal open annulus. -/
abbrev AxisAnnulus (a : ℝ) := {x : Annulus a // (x : Plane) 1 = 0}

/-- The literal inclusion, with the inherited subtype topology. -/
def axisAnnulusInclusion (a : ℝ) : C(AxisAnnulus a, Annulus a) :=
  ⟨Subtype.val, continuous_subtype_val⟩

@[simp] theorem axisAnnulusInclusion_apply (a : ℝ) (x : AxisAnnulus a) :
    axisAnnulusInclusion a x = x.1 := rfl

theorem axisAnnulus_ne_zero (a : ℝ) (ha : 0 ≤ a) (x : AxisAnnulus a) :
    (x.1 : Plane) ≠ 0 :=
  (cellGauge_pos_iff _).mp (ha.trans_lt x.1.2.1)

/-- A fixed transverse direction on the actual gauge-one frontier. -/
def axisAnnulusDirection : Plane := ![0, (1 / 2 : ℝ)]

@[simp] theorem axisAnnulusDirection_gauge : cellGauge axisAnnulusDirection = 1 := by
  norm_num [axisAnnulusDirection, cellGauge]

/-- The transverse affine interpolation before radial normalization. -/
def axisAnnulusBlend (a : ℝ) (s : unitInterval) (x : AxisAnnulus a) : Plane :=
  (1 - (s : ℝ)) • (x.1 : Plane) + (s : ℝ) • axisAnnulusDirection

@[simp] theorem axisAnnulusBlend_zero (a : ℝ) (x : AxisAnnulus a) :
    axisAnnulusBlend a 0 x = (x.1 : Plane) := by
  simp [axisAnnulusBlend]

@[simp] theorem axisAnnulusBlend_one (a : ℝ) (x : AxisAnnulus a) :
    axisAnnulusBlend a 1 x = axisAnnulusDirection := by
  simp [axisAnnulusBlend]

theorem axisAnnulusBlend_second (a : ℝ) (s : unitInterval) (x : AxisAnnulus a) :
    axisAnnulusBlend a s x 1 = (s : ℝ) / 2 := by
  simp [axisAnnulusBlend, axisAnnulusDirection, x.2, div_eq_mul_inv]

theorem axisAnnulusBlend_ne_zero (a : ℝ) (ha : 0 ≤ a)
    (s : unitInterval) (x : AxisAnnulus a) : axisAnnulusBlend a s x ≠ 0 := by
  intro hzero
  have hs : (s : ℝ) = 0 := by
    have h := congrFun hzero 1
    rw [axisAnnulusBlend_second] at h
    change (s : ℝ) / 2 = 0 at h
    linarith
  apply axisAnnulus_ne_zero a ha x
  simpa [axisAnnulusBlend, hs] using hzero

theorem axisAnnulusBlend_gauge_pos (a : ℝ) (ha : 0 ≤ a)
    (s : unitInterval) (x : AxisAnnulus a) : 0 < cellGauge (axisAnnulusBlend a s x) :=
  (cellGauge_pos_iff _).mpr (axisAnnulusBlend_ne_zero a ha s x)

theorem axisAnnulusBlend_continuous (a : ℝ) :
    Continuous (fun p : unitInterval × AxisAnnulus a => axisAnnulusBlend a p.1 p.2) := by
  have hx : Continuous (fun p : unitInterval × AxisAnnulus a => (p.2.1 : Plane)) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul hx).add
    ((continuous_subtype_val.comp continuous_fst).smul continuous_const)

/-- Interpolate the actual gauge radius to the midpoint of the open range. -/
def axisAnnulusRadius (a : ℝ) (s : unitInterval) (x : AxisAnnulus a) : ℝ :=
  radiusBlend ((a + 1) / 2) s (cellGauge (x.1 : Plane))

@[simp] theorem axisAnnulusRadius_zero (a : ℝ) (x : AxisAnnulus a) :
    axisAnnulusRadius a 0 x = cellGauge (x.1 : Plane) := by
  simp [axisAnnulusRadius, radiusBlend]

@[simp] theorem axisAnnulusRadius_one (a : ℝ) (x : AxisAnnulus a) :
    axisAnnulusRadius a 1 x = (a + 1) / 2 := by
  simp [axisAnnulusRadius, radiusBlend]

theorem axisAnnulusRadius_mem (a : ℝ) (ha1 : a < 1)
    (s : unitInterval) (x : AxisAnnulus a) : axisAnnulusRadius a s x ∈ Ioo a 1 :=
  radiusBlend_mem (convex_Ioo a 1) ((a + 1) / 2)
    ⟨by linarith, by linarith⟩ s _ x.1.2

theorem axisAnnulusRadius_continuous (a : ℝ) :
    Continuous (fun p : unitInterval × AxisAnnulus a => axisAnnulusRadius a p.1 p.2) := by
  have hx : Continuous (fun p : unitInterval × AxisAnnulus a => (p.2.1 : Plane)) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
    (cellGauge_continuous.comp hx)).add
      ((continuous_subtype_val.comp continuous_fst).mul continuous_const)

/-- The constant endpoint is a literal midpoint-radius point in the annulus. -/
def axisAnnulusContractionPoint (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) : Annulus a :=
  ⟨((a + 1) / 2) • axisAnnulusDirection, by
    rw [cellGauge_smul_of_nonneg _ (by linarith : 0 ≤ (a + 1) / 2),
      axisAnnulusDirection_gauge, mul_one]
    constructor <;> linarith⟩

@[simp] theorem axisAnnulusContractionPoint_coe (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    (axisAnnulusContractionPoint a ha ha1 : Plane) =
      ((a + 1) / 2) • axisAnnulusDirection := rfl

private theorem axisAnnulusContractFormula_gauge (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (s : unitInterval) (x : AxisAnnulus a) :
    cellGauge ((axisAnnulusRadius a s x / cellGauge (axisAnnulusBlend a s x)) •
      axisAnnulusBlend a s x) = axisAnnulusRadius a s x := by
  have hz := axisAnnulusBlend_gauge_pos a ha s x
  have hr := ha.trans_lt (axisAnnulusRadius_mem a ha1 s x).1
  rw [cellGauge_smul_of_nonneg _ (div_nonneg hr.le hz.le), div_mul_cancel₀ _ hz.ne']

/-- The explicit gauge-rescaled transverse homotopy in the actual annulus. -/
def axisAnnulusContract (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (s : unitInterval) (x : AxisAnnulus a) : Annulus a :=
  ⟨(axisAnnulusRadius a s x / cellGauge (axisAnnulusBlend a s x)) • axisAnnulusBlend a s x,
    by
      rw [axisAnnulusContractFormula_gauge a ha ha1 s x]
      exact axisAnnulusRadius_mem a ha1 s x⟩

@[simp] theorem axisAnnulusContract_coe (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (s : unitInterval) (x : AxisAnnulus a) :
    (axisAnnulusContract a ha ha1 s x : Plane) =
      (axisAnnulusRadius a s x / cellGauge (axisAnnulusBlend a s x)) •
        axisAnnulusBlend a s x := rfl

theorem axisAnnulusContract_gauge (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (s : unitInterval) (x : AxisAnnulus a) :
    cellGauge (axisAnnulusContract a ha ha1 s x : Plane) = axisAnnulusRadius a s x :=
  axisAnnulusContractFormula_gauge a ha ha1 s x

theorem axisAnnulusContract_continuous (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    Continuous (fun p : unitInterval × AxisAnnulus a => axisAnnulusContract a ha ha1 p.1 p.2) :=
  (((axisAnnulusRadius_continuous a).div
    (cellGauge_continuous.comp (axisAnnulusBlend_continuous a))
      (fun p => (axisAnnulusBlend_gauge_pos a ha p.1 p.2).ne')).smul
        (axisAnnulusBlend_continuous a)).subtype_mk _

@[simp] theorem axisAnnulusContract_zero (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (x : AxisAnnulus a) : axisAnnulusContract a ha ha1 0 x = x.1 := by
  apply Subtype.ext
  simp only [axisAnnulusContract_coe, axisAnnulusRadius_zero, axisAnnulusBlend_zero,
    div_self (ha.trans_lt x.1.2.1).ne', one_smul]

@[simp] theorem axisAnnulusContract_one (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (x : AxisAnnulus a) :
    axisAnnulusContract a ha ha1 1 x = axisAnnulusContractionPoint a ha ha1 := by
  apply Subtype.ext
  simp only [axisAnnulusContract_coe, axisAnnulusRadius_one, axisAnnulusBlend_one,
    axisAnnulusDirection_gauge, div_one, axisAnnulusContractionPoint_coe]

/-- The literal axis inclusion is nullhomotopic inside the actual annulus. -/
def axisAnnulusContraction (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    (axisAnnulusInclusion a).Homotopy
      (ContinuousMap.const (AxisAnnulus a) (axisAnnulusContractionPoint a ha ha1)) where
  toFun p := axisAnnulusContract a ha ha1 p.1 p.2
  continuous_toFun := axisAnnulusContract_continuous a ha ha1
  map_zero_left := axisAnnulusContract_zero a ha ha1
  map_one_left := axisAnnulusContract_one a ha ha1

@[simp] theorem axisAnnulusContraction_apply (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (s : unitInterval) (x : AxisAnnulus a) :
    axisAnnulusContraction a ha ha1 (s, x) = axisAnnulusContract a ha ha1 s x := rfl

theorem axisAnnulusInclusion_nullhomotopic (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    (axisAnnulusInclusion a).Nullhomotopic :=
  ⟨axisAnnulusContractionPoint a ha ha1, ⟨axisAnnulusContraction a ha ha1⟩⟩

end Wikipedia.HopfProblem.CuspBoundaryTopVanishing
