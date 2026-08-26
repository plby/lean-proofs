import ErdosProblems.Erdos421.SieveWindowErrors

/-! # Relative control of the actual rough-number window -/

namespace Erdos421

theorem canonicalUpperMain_le_one_add {D z : ℕ} (hD : 0 < D) (hz : 2 ≤ z)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlevel : 16 * Real.exp 1 + 33 + Real.log (32 / ε) ≤ Real.log D / Real.log z) :
    canonicalUpperMain D z ≤ (1 + ε) * roughEulerProduct z := by
  have hlog : Real.log (2 / ε) ≤ Real.log (32 / ε) :=
    Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by norm_num) hε.le)
  have he := exp_rankin_error_le (D := D) (z := (z : ℝ)) hε (by linarith)
  apply (canonicalUpperMain_le_exp_error hD hz (by linarith)).trans
  exact mul_le_mul_of_nonneg_right (by linarith) (roughEulerProduct_pos z).le

theorem additiveRoughWindow_relative_control {D z : ℕ} (hD : 0 < D) (hz : 2 ≤ z)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlevel : 16 * Real.exp 1 + 33 + Real.log (32 / ε) ≤ Real.log D / Real.log z)
    {Y x : ℝ} (hY : 0 < Y) (hx : 0 ≤ x) {B : ℕ} (hB : x + Y ≤ B) :
    |additiveRoughWindow B z Y x - roughEulerProduct z| ≤ ε * roughEulerProduct z +
      ‖sieveWindowError (D ^ 2) (canonicalUpperSieve D z) Y x‖ +
      ‖sieveWindowError (z * D ^ 2) (lowerSieveCoefficient D z) Y x‖ := by
  have hu := additiveRoughWindow_le_main_error hD z hY hx hB
  have hl := additiveRoughWindow_ge_main_error hD (show 1 ≤ z by omega) hY hx hB
  have humain := canonicalUpperMain_le_one_add hD hz hε hε1 hlevel
  have hlmain := canonicalLowerMain_ge_one_sub hD hz hε hε1 hlevel
  have hnormu := norm_nonneg (sieveWindowError (D ^ 2) (canonicalUpperSieve D z) Y x)
  have hnorml := norm_nonneg (sieveWindowError (z * D ^ 2) (lowerSieveCoefficient D z) Y x)
  apply abs_le.mpr
  constructor <;> linarith

theorem sieveWindowError_continuous (M : ℕ) (a : ℕ → ℝ) {Y : ℝ} (hY : 0 < Y) :
    Continuous (sieveWindowError M a Y) := by
  apply continuous_finsetSum
  intro m hm
  exact continuous_const.mul ((additiveDivisorWindow_continuous oneSidedSchwartzWindow hY
    (Finset.mem_Icc.mp hm).1).sub continuous_const)

theorem additiveRoughWindow_continuous (B z : ℕ) (Y : ℝ) :
    Continuous (additiveRoughWindow B z Y) := by
  apply continuous_finsetSum
  intro n hn
  apply Continuous.mul _ continuous_const
  unfold additiveIntegerWeight
  have harg : Continuous (fun x : ℝ ↦ (x - (n : ℝ)) / Y) :=
    (continuous_id.sub continuous_const).div_const Y
  exact Complex.continuous_re.comp
    ((oneSidedSchwartzWindow.continuous.comp harg).const_smul (Y⁻¹ : ℝ))

end Erdos421
