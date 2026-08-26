import ErdosProblems.Erdos421.LogRootPower
import ErdosProblems.Erdos421.LogShiftScale

/-! # Polynomial-degree power savings for logarithmic exponential sums -/

namespace Erdos421

noncomputable def logarithmicPowerConstant (k r : ℕ) : ℝ :=
  logarithmicMeanValueConstant k r ^ (((2 * ((r + 1) * k) : ℕ) : ℝ)⁻¹) + 4

theorem logarithmicRangeSum_power_saving {k : ℕ} (hk : 12 ≤ k) (r N : ℕ)
    (hr : 2 * (k : ℝ) * Real.log k ≤ r) {A t : ℝ} (hA : 1 ≤ A)
    (hNA : (N : ℝ) ≤ A) (htlower : A ^ (k - 1) ≤ |t|) (htupper : |t| ≤ A ^ k) :
    ‖logarithmicRangeSum A N t‖ ≤ logarithmicPowerConstant k r *
      A ^ (1 - 1 / (4 * (((r + 1) * k : ℕ) : ℝ))) := by
  have hkpos : 0 < k := by omega
  have hAp : 0 < A := by linarith
  have hT : 0 < |t| := (pow_pos hAp (k - 1)).trans_le htlower
  have ht : t ≠ 0 := abs_pos.mp hT
  have hs : 0 < (r + 1) * k := Nat.mul_pos (Nat.succ_pos r) hkpos
  let p := 2 * ((r + 1) * k)
  let M := logarithmicShiftLength k A |t|
  let C := logarithmicMeanValueConstant k r
  have hp : 0 < p := Nat.mul_pos (by decide : 0 < 2) hs
  have hM : 0 < M := logarithmicShiftLength_pos k hA hT htupper
  have hMR : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hC : 0 ≤ C := logarithmicMeanValueConstant_nonneg k r
  have hscaleUpper : |t| * (M : ℝ) ^ (k + 1) ≤ A ^ (k + 1) :=
    logarithmicShiftLength_scale_upper k hAp hT
  have hscaleLower : A ^ (k + 1) ≤ |t| * (2 * (M : ℝ)) ^ (k + 1) :=
    logarithmicShiftLength_scale_lower k hA hT htupper
  have hmean := logarithmicRangeSum_meanValue_bound hkpos hM hs N ht hAp htupper hscaleUpper
  have hmom := logarithmicMomentUpper_le_power (by omega : 2 ≤ k) hM r hr hAp ht hNA hscaleLower
  have hU : 0 ≤ logarithmicMomentUpper k ((r + 1) * k) M N t A := by
    unfold logarithmicMomentUpper
    positivity
  have hfull : (N : ℝ) ^ (p - 1) * logarithmicMomentUpper k ((r + 1) * k) M N t A ≤
      A ^ (p - 1) * (C * (M : ℝ) ^ (p + 3)) :=
    mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg N) hNA _) hmom hU (pow_nonneg hAp.le _)
  have hroot := Real.rpow_le_rpow (mul_nonneg (pow_nonneg (Nat.cast_nonneg N) _) hU)
    hfull (by positivity : 0 ≤ (p : ℝ)⁻¹)
  have hb : ‖logarithmicRangeSum A N t‖ ≤
      (A ^ (p - 1) * (C * (M : ℝ) ^ (p + 3))) ^ ((p : ℝ)⁻¹) / M + 4 * M :=
    hmean.trans (add_le_add (div_le_div_of_nonneg_right hroot hMR.le) le_rfl)
  have heighth : 2 / ((k + 1 : ℕ) : ℝ) ≤ (1 / 6 : ℝ) := by
    have hkR : (12 : ℝ) ≤ k := by exact_mod_cast hk
    apply (div_le_iff₀ (by positivity)).mpr
    push_cast
    linarith
  have hMA : (M : ℝ) ≤ A ^ (1 / 6 : ℝ) :=
    (logarithmicShiftLength_le_power hkpos hA hT htlower).trans
      (Real.rpow_le_rpow_of_exponent_le hA heighth)
  have hfinal := hb.trans (logarithmic_moment_root_power_bound hp hA hMR hC hMA)
  have he : 1 - (p : ℝ)⁻¹ / 2 = 1 - 1 / (4 * (((r + 1) * k : ℕ) : ℝ)) := by
    dsimp only [p]
    push_cast
    field_simp
    ring
  change ‖logarithmicRangeSum A N t‖ ≤ logarithmicPowerConstant k r *
    A ^ (1 - (p : ℝ)⁻¹ / 2) at hfinal
  rw [he] at hfinal
  exact hfinal

theorem logarithmicSum_meanValue_power_saving {k A N : ℕ} (hk : 12 ≤ k) (hA : 0 < A)
    (hNA : N ≤ A) (r : ℕ) (hr : 2 * (k : ℝ) * Real.log k ≤ r) {t : ℝ}
    (htlower : (A : ℝ) ^ (k - 1) ≤ |t|) (htupper : |t| ≤ (A : ℝ) ^ k) :
    ‖logarithmicSum A N t‖ ≤ logarithmicPowerConstant k r *
      (A : ℝ) ^ (1 - 1 / (4 * (((r + 1) * k : ℕ) : ℝ))) := by
  rw [← logarithmicRangeSum_nat]
  exact logarithmicRangeSum_power_saving hk r N hr (by exact_mod_cast hA)
    (Nat.cast_le.mpr hNA) htlower htupper

end Erdos421
