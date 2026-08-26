import ErdosProblems.Erdos1002.ProbabilityFoundations
import Mathlib.MeasureTheory.Measure.Stieltjes

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The Gauss probability measure and one-digit cylinders

The continued-fraction argument uses the probability measure with distribution
function `log (1+x) / log 2` on `[0,1]`.  We construct it as a Stieltjes
measure, including the constant extensions outside `[0,1]`, and compute the
measure of the first-digit cylinders exactly.
-/

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace Erdos1002

noncomputable section

/-- Clamp a real number to `[0,1]`. -/
def unitClamp (x : ℝ) : ℝ := max 0 (min x 1)

theorem unitClamp_nonneg (x : ℝ) : 0 ≤ unitClamp x := by
  exact le_max_left _ _

theorem unitClamp_le_one (x : ℝ) : unitClamp x ≤ 1 := by
  exact max_le (by norm_num) (min_le_right _ _)

theorem unitClamp_mono : Monotone unitClamp := by
  intro x y hxy
  unfold unitClamp
  exact max_le_max_left 0 (min_le_min_right 1 hxy)

theorem unitClamp_eq_of_mem_Icc {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    unitClamp x = x := by
  simp [unitClamp, hx.1, hx.2]

theorem unitClamp_eq_zero_of_le {x : ℝ} (hx : x ≤ 0) :
    unitClamp x = 0 := by
  simp [unitClamp, hx]

theorem unitClamp_eq_one_of_le {x : ℝ} (hx : 1 ≤ x) :
    unitClamp x = 1 := by
  simp [unitClamp, hx]

/-- Continuous distribution function of Gauss measure, extended constantly
outside the unit interval. -/
def gaussCDF (x : ℝ) : ℝ :=
  Real.log (1 + unitClamp x) / Real.log 2

theorem continuous_gaussCDF : Continuous gaussCDF := by
  unfold gaussCDF
  have hc : Continuous (fun x : ℝ ↦ 1 + unitClamp x) := by
    unfold unitClamp
    fun_prop
  exact (hc.log (fun x ↦ ne_of_gt (by
    linarith [unitClamp_nonneg x]))).div_const _

theorem gaussCDF_mono : Monotone gaussCDF := by
  intro x y hxy
  have hclamp : unitClamp x ≤ unitClamp y := unitClamp_mono hxy
  have hxpos : 0 < 1 + unitClamp x := by
    linarith [unitClamp_nonneg x]
  have hypos : 0 < 1 + unitClamp y := by
    linarith [unitClamp_nonneg y]
  have hlog : Real.log (1 + unitClamp x) ≤
      Real.log (1 + unitClamp y) := by
    exact (Real.strictMonoOn_log.le_iff_le
      (a := 1 + unitClamp x) (b := 1 + unitClamp y) hxpos hypos).mpr
        (by linarith)
  exact (div_le_div_iff_of_pos_right (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hlog

def gaussStieltjes : StieltjesFunction ℝ where
  toFun := gaussCDF
  mono' := gaussCDF_mono
  right_continuous' := fun _ ↦ continuous_gaussCDF.continuousWithinAt

theorem gaussCDF_eq_zero_of_le {x : ℝ} (hx : x ≤ 0) :
    gaussCDF x = 0 := by
  rw [gaussCDF, unitClamp_eq_zero_of_le hx]
  simp

theorem gaussCDF_eq_one_of_le {x : ℝ} (hx : 1 ≤ x) :
    gaussCDF x = 1 := by
  rw [gaussCDF, unitClamp_eq_one_of_le hx]
  norm_num

theorem tendsto_gaussCDF_atBot : Tendsto gaussCDF atBot (nhds 0) := by
  have h : gaussCDF =ᶠ[atBot] fun _ ↦ 0 := by
    filter_upwards [eventually_le_atBot (0 : ℝ)] with x hx
    exact gaussCDF_eq_zero_of_le hx
  rw [tendsto_congr' h]
  exact tendsto_const_nhds

theorem tendsto_gaussCDF_atTop : Tendsto gaussCDF atTop (nhds 1) := by
  have h : gaussCDF =ᶠ[atTop] fun _ ↦ 1 := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact gaussCDF_eq_one_of_le hx
  rw [tendsto_congr' h]
  exact tendsto_const_nhds

/-- Gauss measure on the real line, supported on `[0,1]`. -/
def gaussMeasure : Measure ℝ := gaussStieltjes.measure

instance gaussMeasure_isProbabilityMeasure : IsProbabilityMeasure gaussMeasure where
  measure_univ := by
    rw [gaussMeasure, gaussStieltjes.measure_univ
      tendsto_gaussCDF_atBot tendsto_gaussCDF_atTop]
    norm_num

def gaussProbability : ProbabilityMeasure ℝ :=
  ⟨gaussMeasure, inferInstance⟩

theorem gaussMeasure_real_Ioc {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    gaussMeasure.real (Ioc a b) =
      (Real.log (1 + b) - Real.log (1 + a)) / Real.log 2 := by
  have haI : a ∈ Icc (0 : ℝ) 1 := ⟨ha, hab.trans hb⟩
  have hbI : b ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hab, hb⟩
  have hdiff : 0 ≤ gaussCDF b - gaussCDF a :=
    sub_nonneg.mpr (gaussCDF_mono hab)
  rw [measureReal_def, gaussMeasure, gaussStieltjes.measure_Ioc,
    show ((gaussStieltjes : ℝ → ℝ) b - (gaussStieltjes : ℝ → ℝ) a) =
      gaussCDF b - gaussCDF a by rfl,
    ENNReal.toReal_ofReal hdiff]
  rw [gaussCDF, gaussCDF, unitClamp_eq_of_mem_Icc haI,
    unitClamp_eq_of_mem_Icc hbI]
  ring

/-- The first regular-continued-fraction digit `q` corresponds to this
half-open cylinder. -/
def firstDigitCylinder (q : ℕ) : Set ℝ :=
  Ioc (1 / ((q + 1 : ℕ) : ℝ)) (1 / (q : ℝ))

theorem gaussMeasure_real_firstDigitCylinder (q : ℕ) (hq : 0 < q) :
    gaussMeasure.real (firstDigitCylinder q) =
      Real.log (((q + 1 : ℕ) : ℝ) ^ 2 /
        ((q : ℝ) * (q + 2 : ℕ))) / Real.log 2 := by
  have hqR : (0 : ℝ) < (q : ℝ) := by positivity
  have hq1R : (0 : ℝ) < ((q + 1 : ℕ) : ℝ) := by positivity
  have hq2R : (0 : ℝ) < ((q + 2 : ℕ) : ℝ) := by positivity
  have hab : 1 / ((q + 1 : ℕ) : ℝ) ≤ 1 / (q : ℝ) := by
    exact one_div_le_one_div_of_le hqR (by exact_mod_cast Nat.le_succ q)
  rw [firstDigitCylinder,
    gaussMeasure_real_Ioc (by positivity) hab (by
      rw [div_le_one hqR]
      exact_mod_cast hq)]
  have h₁ : 1 + 1 / (q : ℝ) = ((q + 1 : ℕ) : ℝ) / (q : ℝ) := by
    field_simp
    norm_num [Nat.cast_add]
  have h₂ : 1 + 1 / ((q + 1 : ℕ) : ℝ) =
      ((q + 2 : ℕ) : ℝ) / ((q + 1 : ℕ) : ℝ) := by
    field_simp
    norm_num [Nat.cast_add]
    ring
  rw [h₁, h₂, ← Real.log_div (by positivity) (by positivity)]
  congr 2
  norm_num [Nat.cast_add]
  field_simp

end

end Erdos1002
