import ErdosProblems.Erdos67b.MRCofactorPowerCutoff
import ErdosProblems.Erdos67b.MRNarrowPrimePartition

/-!
# The source auxiliary logarithmic schedule

At logarithmic scale `R`, use lower endpoint `R^(47/48)`, upper endpoint
`R/log R`, and resolution `R^(1/48)`. Their exact ratio and elementary
limits discharge separation, width, and narrow subblock range conditions.
-/

open Filter
open scoped Topology

namespace Erdos67b

noncomputable section

def mrAuxiliaryResolution (R : ℝ) : ℝ := R ^ (1 / 48 : ℝ)

def mrAuxiliaryLogLower (R : ℝ) : ℝ := R ^ (47 / 48 : ℝ)

def mrAuxiliaryLogUpper (R : ℝ) : ℝ := R / Real.log R

theorem mrAuxiliary_lower_mul_resolution {R : ℝ} (hR : 0 < R) :
    mrAuxiliaryLogLower R * mrAuxiliaryResolution R = R := by
  unfold mrAuxiliaryLogLower mrAuxiliaryResolution
  rw [← Real.rpow_add hR]
  norm_num

theorem mrAuxiliary_log_ratio {R : ℝ} (hR : 1 < R) :
    mrAuxiliaryLogLower R / mrAuxiliaryLogUpper R =
      Real.log R / mrAuxiliaryResolution R := by
  have hRpos : 0 < R := by linarith
  have hH : 0 < mrAuxiliaryResolution R := Real.rpow_pos_of_pos hRpos _
  have ha : 0 < mrAuxiliaryLogLower R := Real.rpow_pos_of_pos hRpos _
  have hl : 0 < Real.log R := Real.log_pos hR
  unfold mrAuxiliaryLogUpper
  calc
    _ = mrAuxiliaryLogLower R * Real.log R / R := by field_simp
    _ = mrAuxiliaryLogLower R * Real.log R /
        (mrAuxiliaryLogLower R * mrAuxiliaryResolution R) :=
      congrArg (fun z : ℝ ↦ mrAuxiliaryLogLower R * Real.log R / z)
        (mrAuxiliary_lower_mul_resolution hRpos).symm
    _ = Real.log R / mrAuxiliaryResolution R := by
      field_simp

theorem mrTendsto_auxiliary_resolution : Tendsto mrAuxiliaryResolution atTop atTop :=
  tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 48)

theorem mrTendsto_auxiliary_lower : Tendsto mrAuxiliaryLogLower atTop atTop :=
  tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 47 / 48)

theorem mrTendsto_auxiliary_log_ratio :
    Tendsto (fun R : ℝ ↦ mrAuxiliaryLogLower R / mrAuxiliaryLogUpper R) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 48)).tendsto_div_nhds_zero
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with R hR
  exact (mrAuxiliary_log_ratio hR).symm

theorem mrAuxiliary_lower_gt_sqrt {R : ℝ} (hR : 1 < R) :
    Real.sqrt R < mrAuxiliaryLogLower R := by
  rw [Real.sqrt_eq_rpow]
  exact Real.rpow_lt_rpow_of_exponent_lt hR (by norm_num : (1 / 2 : ℝ) < 47 / 48)

theorem mrEventually_auxiliary_schedule :
    ∀ᶠ R : ℝ in atTop,
      1 < R ∧ 4 ≤ mrAuxiliaryResolution R ∧ 4 ≤ mrAuxiliaryLogLower R ∧
      2 * mrAuxiliaryLogLower R ≤ mrAuxiliaryLogUpper R ∧
      Real.sqrt R < mrAuxiliaryLogLower R ∧
      ∀ r ∈ mrLogBlockIndices (mrAuxiliaryResolution R)
          (mrAuxiliaryLogLower R) (mrAuxiliaryLogUpper R),
        3 ≤ (r : ℝ) / mrAuxiliaryResolution R ∧
          (r : ℝ) / mrAuxiliaryResolution R ≤ mrAuxiliaryLogUpper R := by
  have hratio := (tendsto_order.1 mrTendsto_auxiliary_log_ratio).2
    (1 / 2) (by norm_num)
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    mrTendsto_auxiliary_resolution.eventually (eventually_ge_atTop 4),
    mrTendsto_auxiliary_lower.eventually (eventually_ge_atTop 4), hratio]
    with R hR hH ha hratioR
  have hb : 0 < mrAuxiliaryLogUpper R := div_pos (by linarith) (Real.log_pos hR)
  have hab : 2 * mrAuxiliaryLogLower R ≤ mrAuxiliaryLogUpper R := by
    have hh := (div_le_iff₀ hb).mp hratioR.le
    linarith
  refine ⟨hR, hH, ha, hab, mrAuxiliary_lower_gt_sqrt hR, ?_⟩
  intro r hr
  have hh := mrLogBlockIndices_parameter_bounds (by linarith : 1 ≤ mrAuxiliaryResolution R)
    (by linarith : 0 ≤ mrAuxiliaryLogLower R) hb.le hr
  exact ⟨by linarith [hh.1], hh.2⟩

end

end Erdos67b
