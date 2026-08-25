/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Util.MaynardTao.Concentration

/-!
# Explicit parameters from the Maynard--Tao cardinal threshold
-/

namespace MaynardTao

noncomputable section

noncomputable def tupleLogMass (K : ℕ) : ℝ :=
  Real.log ((K : ℝ) * Real.log K)

noncomputable def sharpDecay (K : ℕ) : ℝ :=
  (5 : ℝ) / 3 * tupleLogMass K

noncomputable def sharpDelta (K : ℕ) : ℝ :=
  (tupleLogMass K)⁻¹

noncomputable def sharpGoodCutoff (K : ℕ) : ℝ :=
  1 - (3 : ℝ) / 2 * sharpDelta K

noncomputable def sharpFiberCutoff (K : ℕ) : ℝ :=
  1 - (5 : ℝ) / 4 * sharpDelta K

noncomputable def sharpGoodMass (K : ℕ) : ℝ :=
  1 - 13 / sharpDecay K

theorem positive_card_log_of_threshold {m K : ℕ}
    (h : Real.exp (8 * (m : ℝ) + 4) <
      (K : ℝ) * Real.log K) :
    0 < (K : ℝ) * Real.log K :=
  (Real.exp_pos _).trans h

theorem card_pos_of_threshold {m K : ℕ}
    (h : Real.exp (8 * (m : ℝ) + 4) <
      (K : ℝ) * Real.log K) :
    0 < K := by
  have hprod := positive_card_log_of_threshold h
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hKR : (0 : ℝ) < K := by
    by_contra hnot
    have hz : (K : ℝ) = 0 := le_antisymm (le_of_not_gt hnot) hK0
    rw [hz, zero_mul] at hprod
    linarith
  exact_mod_cast hKR

theorem log_card_pos_of_threshold {m K : ℕ}
    (h : Real.exp (8 * (m : ℝ) + 4) <
      (K : ℝ) * Real.log K) :
    0 < Real.log K := by
  have hprod := positive_card_log_of_threshold h
  have hKR : (0 : ℝ) < K := by exact_mod_cast card_pos_of_threshold h
  rcases (mul_pos_iff.mp hprod) with hp | hp
  · exact hp.2
  · exact False.elim ((not_lt_of_ge hKR.le) hp.1)

theorem two_le_card_of_threshold {m K : ℕ}
    (h : Real.exp (8 * (m : ℝ) + 4) <
      (K : ℝ) * Real.log K) :
    2 ≤ K := by
  have hlog := log_card_pos_of_threshold h
  have hKone : (1 : ℝ) < K := (Real.log_pos_iff (by
    exact Nat.cast_nonneg K)).mp hlog
  have hKnat : 1 < K := by exact_mod_cast hKone
  omega

theorem logMass_gt_threshold {m K : ℕ}
    (h : Real.exp (8 * (m : ℝ) + 4) <
      (K : ℝ) * Real.log K) :
    8 * (m : ℝ) + 4 < tupleLogMass K := by
  have hright : 0 < (K : ℝ) * Real.log K :=
    positive_card_log_of_threshold h
  have hmono := Real.strictMonoOn_log (Real.exp_pos _)
    hright h
  simpa [tupleLogMass] using hmono

theorem logMass_gt_twenty {m K : ℕ} (hm : 2 ≤ m)
    (h : Real.exp (8 * (m : ℝ) + 4) <
      (K : ℝ) * Real.log K) :
    20 < tupleLogMass K := by
  have ht := logMass_gt_threshold h
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  linarith

theorem sharpDecay_pos {m K : ℕ} (hm : 2 ≤ m)
    (h : Real.exp (8 * (m : ℝ) + 4) <
      (K : ℝ) * Real.log K) :
    0 < sharpDecay K := by
  unfold sharpDecay
  exact mul_pos (by norm_num) (by linarith [logMass_gt_twenty hm h])

theorem sharpDecay_gt_thirty {m K : ℕ} (hm : 2 ≤ m)
    (h : Real.exp (8 * (m : ℝ) + 4) <
      (K : ℝ) * Real.log K) :
    30 < sharpDecay K := by
  unfold sharpDecay
  nlinarith [logMass_gt_twenty hm h]

theorem sharpDelta_pos {m K : ℕ} (hm : 2 ≤ m)
    (h : Real.exp (8 * (m : ℝ) + 4) <
      (K : ℝ) * Real.log K) :
    0 < sharpDelta K := by
  unfold sharpDelta
  exact inv_pos.mpr (by linarith [logMass_gt_twenty hm h])

theorem sharpDelta_lt_one_twentieth {m K : ℕ} (hm : 2 ≤ m)
    (h : Real.exp (8 * (m : ℝ) + 4) <
      (K : ℝ) * Real.log K) :
    sharpDelta K < (1 : ℝ) / 20 := by
  unfold sharpDelta
  have hL := logMass_gt_twenty hm h
  calc
    (tupleLogMass K)⁻¹ < (20 : ℝ)⁻¹ :=
      by simpa only [one_div] using
        (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 20) hL)
    _ = (1 : ℝ) / 20 := by norm_num

theorem sharpGoodCutoff_add_delta_le_one (K : ℕ)
    (hδ : 0 ≤ sharpDelta K) :
    sharpGoodCutoff K + sharpDelta K ≤ 1 := by
  unfold sharpGoodCutoff
  linarith

theorem sharpGoodCutoff_lt_fiberCutoff {m K : ℕ} (hm : 2 ≤ m)
    (h : Real.exp (8 * (m : ℝ) + 4) <
      (K : ℝ) * Real.log K) :
    sharpGoodCutoff K < sharpFiberCutoff K := by
  unfold sharpGoodCutoff sharpFiberCutoff
  have hδ := sharpDelta_pos hm h
  linarith

theorem sharpFiberCutoff_lt_one {m K : ℕ} (hm : 2 ≤ m)
    (h : Real.exp (8 * (m : ℝ) + 4) <
      (K : ℝ) * Real.log K) :
    sharpFiberCutoff K < 1 := by
  unfold sharpFiberCutoff
  have hδ := sharpDelta_pos hm h
  linarith

theorem sharpFiberCutoff_add_delta_lt_one {m K : ℕ} (hm : 2 ≤ m)
    (h : Real.exp (8 * (m : ℝ) + 4) <
      (K : ℝ) * Real.log K) :
    sharpFiberCutoff K + sharpDelta K < 1 := by
  unfold sharpFiberCutoff
  have hδ := sharpDelta_pos hm h
  linarith

theorem sharpGoodMass_pos {m K : ℕ} (hm : 2 ≤ m)
    (h : Real.exp (8 * (m : ℝ) + 4) <
      (K : ℝ) * Real.log K) :
    0 < sharpGoodMass K := by
  unfold sharpGoodMass
  have hA := sharpDecay_gt_thirty hm h
  have hApos := sharpDecay_pos hm h
  rw [sub_pos, div_lt_iff₀ hApos]
  linarith

theorem sharpCandidate_ratio_gt_logCard_sq_div_decay
    {m K : ℕ} (hm : 2 ≤ m)
    (h : Real.exp (8 * (m : ℝ) + 4) <
      (K : ℝ) * Real.log K)
    (hmean : ((K - 1 : ℕ) : ℝ) *
      variableCoordinateMean K (sharpDecay K) < sharpGoodCutoff K)
    (hvariance :
      (sharpGoodCutoff K - ((K - 1 : ℕ) : ℝ) *
          variableCoordinateMean K (sharpDecay K))⁻¹ ^ 2 *
          (((K - 1 : ℕ) : ℝ) *
            variableSecondMoment K (sharpDecay K) *
            Erdos4.VariableMaynard.baseMass K (sharpDecay K) ^ (K - 1 - 1)) <
        (1 - sharpGoodMass K) *
          Erdos4.VariableMaynard.baseMass K (sharpDecay K) ^ (K - 1)) :
    sharpGoodMass K * Real.log K ^ 2 / sharpDecay K <
      BoundedGaps.Maynard.maynardRatio K
        (Erdos4.VariableMaynard.candidate K (sharpDecay K)) := by
  have hK2 := two_le_card_of_threshold h
  have hK : 0 < K := card_pos_of_threshold h
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hlogK : 0 < Real.log K := log_card_pos_of_threshold h
  have hA : 0 < sharpDecay K := sharpDecay_pos hm h
  have hδ : 0 < sharpDelta K := sharpDelta_pos hm h
  have hδlt : sharpDelta K < (1 : ℝ) / 20 :=
    sharpDelta_lt_one_twentieth hm h
  have hδ1 : sharpDelta K ≤ 1 := by linarith
  have hγ : 0 < sharpGoodMass K := sharpGoodMass_pos hm h
  have hratio := maynardRatio_variableCandidate_gt_of_concentration
    (K := K) (A := sharpDecay K) (q := sharpGoodCutoff K)
    (δ := sharpDelta K) (γ := sharpGoodMass K)
    hK2 hA hδ hδ1 (by
      exact sharpGoodCutoff_add_delta_le_one K hδ.le) hγ hmean hvariance
  have hL : 0 < tupleLogMass K := by
    linarith [logMass_gt_twenty hm h]
  have harg : (K : ℝ) <
      1 + sharpDecay K * (K : ℝ) * sharpDelta K := by
    unfold sharpDecay sharpDelta
    have hcancel : tupleLogMass K * (tupleLogMass K)⁻¹ = 1 := by
      field_simp [hL.ne']
    rw [show (5 : ℝ) / 3 * tupleLogMass K * (K : ℝ) *
        (tupleLogMass K)⁻¹ = (5 : ℝ) / 3 * (K : ℝ) by
      field_simp [hL.ne']]
    linarith
  have hargpos : 0 <
      1 + sharpDecay K * (K : ℝ) * sharpDelta K :=
    hKR.trans harg
  have hlogarg : Real.log K <
      Real.log (1 + sharpDecay K * (K : ℝ) * sharpDelta K) :=
    Real.strictMonoOn_log hKR hargpos harg
  have hlogarg0 : 0 < Real.log
      (1 + sharpDecay K * (K : ℝ) * sharpDelta K) :=
    hlogK.trans hlogarg
  have hsq : Real.log K ^ 2 <
      Real.log (1 + sharpDecay K * (K : ℝ) * sharpDelta K) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hlogarg)
      (add_pos hlogK hlogarg0)]
  have hfac : 1 <
      (1 + sharpDecay K * (K : ℝ)) /
        (sharpDecay K * (K : ℝ)) := by
    rw [lt_div_iff₀ (mul_pos hA hKR)]
    linarith
  have hfirst : sharpGoodMass K * Real.log K ^ 2 / sharpDecay K <
      sharpGoodMass K *
        Real.log (1 + sharpDecay K * (K : ℝ) * sharpDelta K) ^ 2 /
          sharpDecay K := by
    exact div_lt_div_of_pos_right
      (mul_lt_mul_of_pos_left hsq hγ) hA
  have hmiddle : sharpGoodMass K *
        Real.log (1 + sharpDecay K * (K : ℝ) * sharpDelta K) ^ 2 /
          sharpDecay K <
      (sharpGoodMass K *
        Real.log (1 + sharpDecay K * (K : ℝ) * sharpDelta K) ^ 2 /
          sharpDecay K) *
        ((1 + sharpDecay K * (K : ℝ)) /
          (sharpDecay K * (K : ℝ))) := by
    have hleft : 0 < sharpGoodMass K *
        Real.log (1 + sharpDecay K * (K : ℝ) * sharpDelta K) ^ 2 /
          sharpDecay K := by positivity
    nlinarith [mul_pos hleft (sub_pos.mpr hfac)]
  have heq :
      (sharpGoodMass K *
        Real.log (1 + sharpDecay K * (K : ℝ) * sharpDelta K) ^ 2 /
          sharpDecay K) *
        ((1 + sharpDecay K * (K : ℝ)) /
          (sharpDecay K * (K : ℝ))) =
      (K : ℝ) * sharpGoodMass K *
        variableShortMass K (sharpDecay K) (sharpDelta K) ^ 2 /
          Erdos4.VariableMaynard.baseMass K (sharpDecay K) := by
    rw [variableShortMass_eq hK hA hδ.le]
    unfold Erdos4.VariableMaynard.baseMass
    field_simp [hA.ne', hKR.ne']
  exact (hfirst.trans (hmiddle.trans_eq heq)).trans hratio

theorem sharp_fullMean_lt_seven_tenths_of_log_bounds
    {m K : ℕ} (hm : 2 ≤ m)
    (h : Real.exp (8 * (m : ℝ) + 4) <
      (K : ℝ) * Real.log K)
    (hlogNumerator :
      Real.log (1 + sharpDecay K * (K : ℝ)) <
        (25 : ℝ) / 24 * tupleLogMass K)
    (hAK : (1000 : ℝ) < sharpDecay K * (K : ℝ)) :
    (K : ℝ) * variableCoordinateMean K (sharpDecay K) <
      (63 : ℝ) / 100 := by
  have hK : 0 < K := card_pos_of_threshold h
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hA : 0 < sharpDecay K := sharpDecay_pos hm h
  have hL : 0 < tupleLogMass K := by
    linarith [logMass_gt_twenty hm h]
  have hfirst := Erdos4.VariableMaynard.firstMoment_le hK hA
  have hmeanRaw : variableCoordinateMean K (sharpDecay K) ≤
      Real.log (1 + sharpDecay K * (K : ℝ)) *
        (1 + sharpDecay K * (K : ℝ)) /
          (sharpDecay K ^ 2 * (K : ℝ) ^ 2) := by
    unfold variableCoordinateMean Erdos4.VariableMaynard.baseMass
    calc
      Erdos4.VariableMaynard.firstMoment K (sharpDecay K) /
          (1 + sharpDecay K * (K : ℝ))⁻¹ ≤
        (Real.log (1 + sharpDecay K * (K : ℝ)) /
          (sharpDecay K ^ 2 * (K : ℝ) ^ 2)) /
            (1 + sharpDecay K * (K : ℝ))⁻¹ :=
        div_le_div_of_nonneg_right hfirst (inv_nonneg.mpr (by positivity))
      _ = Real.log (1 + sharpDecay K * (K : ℝ)) *
          (1 + sharpDecay K * (K : ℝ)) /
            (sharpDecay K ^ 2 * (K : ℝ) ^ 2) := by
        field_simp [hA.ne', hKR.ne']
  have hfac : (1 + sharpDecay K * (K : ℝ)) /
      (sharpDecay K * (K : ℝ)) < (1001 : ℝ) / 1000 := by
    rw [div_lt_iff₀ (mul_pos hA hKR)]
    nlinarith
  have hrew : (K : ℝ) *
      (Real.log (1 + sharpDecay K * (K : ℝ)) *
        (1 + sharpDecay K * (K : ℝ)) /
          (sharpDecay K ^ 2 * (K : ℝ) ^ 2)) =
      (Real.log (1 + sharpDecay K * (K : ℝ)) / sharpDecay K) *
        ((1 + sharpDecay K * (K : ℝ)) /
          (sharpDecay K * (K : ℝ))) := by
    field_simp [hA.ne', hKR.ne']
  have hlogRatio : Real.log (1 + sharpDecay K * (K : ℝ)) /
      sharpDecay K < (5 : ℝ) / 8 := by
    calc
      Real.log (1 + sharpDecay K * (K : ℝ)) / sharpDecay K <
          ((25 : ℝ) / 24 * tupleLogMass K) / sharpDecay K :=
        div_lt_div_of_pos_right hlogNumerator hA
      _ = (5 : ℝ) / 8 := by
        unfold sharpDecay
        field_simp [hL.ne']
        norm_num
  calc
    (K : ℝ) * variableCoordinateMean K (sharpDecay K) ≤
        (K : ℝ) *
          (Real.log (1 + sharpDecay K * (K : ℝ)) *
            (1 + sharpDecay K * (K : ℝ)) /
              (sharpDecay K ^ 2 * (K : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hmeanRaw hKR.le
    _ = (Real.log (1 + sharpDecay K * (K : ℝ)) / sharpDecay K) *
        ((1 + sharpDecay K * (K : ℝ)) /
          (sharpDecay K * (K : ℝ))) := hrew
    _ < (5 : ℝ) / 8 *
        ((1 + sharpDecay K * (K : ℝ)) /
          (sharpDecay K * (K : ℝ))) :=
      mul_lt_mul_of_pos_right hlogRatio (by positivity)
    _ < (5 : ℝ) / 8 * ((1001 : ℝ) / 1000) :=
      mul_lt_mul_of_pos_left hfac (by norm_num)
    _ < (63 : ℝ) / 100 := by norm_num

theorem tupleLogMass_eq_logCard_add_logLogCard
    {m K : ℕ}
    (h : Real.exp (8 * (m : ℝ) + 4) <
      (K : ℝ) * Real.log K) :
    tupleLogMass K = Real.log K + Real.log (Real.log K) := by
  unfold tupleLogMass
  have hK : (0 : ℝ) < K := by exact_mod_cast card_pos_of_threshold h
  have hlogK : 0 < Real.log K := log_card_pos_of_threshold h
  rw [Real.log_mul hK.ne' hlogK.ne']

theorem logCard_gt_sixteen {m K : ℕ} (hm : 2 ≤ m)
    (h : Real.exp (8 * (m : ℝ) + 4) <
      (K : ℝ) * Real.log K) :
    (16 : ℝ) < Real.log K := by
  have hL := logMass_gt_twenty hm h
  have hlogK : 0 < Real.log K := log_card_pos_of_threshold h
  have hexp3 : (16 : ℝ) < Real.exp 3 := by
    calc
      (16 : ℝ) < (27 / 10 : ℝ) ^ 3 := by norm_num
      _ < Real.exp 1 ^ 3 := by
        gcongr
        exact (by norm_num : (27 / 10 : ℝ) < 2.7182818283).trans
          Real.exp_one_gt_d9
      _ = Real.exp 3 := by
        simpa using (Real.exp_one_pow 3)
  have hlog16 : Real.log (16 : ℝ) < 3 :=
    (Real.log_lt_iff_lt_exp (by norm_num)).2 hexp3
  by_contra hnot
  have hx16 : Real.log K ≤ 16 := le_of_not_gt hnot
  have hloglog : Real.log (Real.log K) ≤ Real.log (16 : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hlogK)
      (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 16))
      hx16
  rw [tupleLogMass_eq_logCard_add_logLogCard h] at hL
  linarith

theorem tupleLogMass_lt_six_fifths_logCard
    {m K : ℕ} (hm : 2 ≤ m)
    (h : Real.exp (8 * (m : ℝ) + 4) <
      (K : ℝ) * Real.log K) :
    tupleLogMass K < (6 : ℝ) / 5 * Real.log K := by
  have hx : (16 : ℝ) < Real.log K := logCard_gt_sixteen hm h
  have hlogK : 0 < Real.log K := log_card_pos_of_threshold h
  have hlog16 : Real.log (16 : ℝ) < 3 := by
    have hexp3 : (16 : ℝ) < Real.exp 3 := by
      calc
        (16 : ℝ) < (27 / 10 : ℝ) ^ 3 := by norm_num
        _ < Real.exp 1 ^ 3 := by
          gcongr
          exact (by norm_num : (27 / 10 : ℝ) < 2.7182818283).trans
            Real.exp_one_gt_d9
        _ = Real.exp 3 := by simpa using (Real.exp_one_pow 3)
    exact (Real.log_lt_iff_lt_exp (by norm_num)).2 hexp3
  have hexpOne : Real.exp 1 ≤ (16 : ℝ) :=
    (Real.exp_one_lt_three.le).trans (by norm_num)
  have hratio : Real.log (Real.log K) / Real.log K ≤
      Real.log (16 : ℝ) / 16 :=
    Real.log_div_self_antitoneOn hexpOne
      (hexpOne.trans (le_of_lt hx)) (le_of_lt hx)
  have hratio' : Real.log (Real.log K) / Real.log K < (1 : ℝ) / 5 := by
    calc
      Real.log (Real.log K) / Real.log K ≤
          Real.log (16 : ℝ) / 16 := hratio
      _ < (3 : ℝ) / 16 :=
        div_lt_div_of_pos_right hlog16 (by norm_num)
      _ < (1 : ℝ) / 5 := by norm_num
  have hloglog : Real.log (Real.log K) < (1 : ℝ) / 5 * Real.log K := by
    have := mul_lt_mul_of_pos_right hratio' hlogK
    field_simp [hlogK.ne'] at this
    nlinarith
  rw [tupleLogMass_eq_logCard_add_logLogCard h]
  linarith

theorem tupleLogMass_lt_nineteen_sixteenths_logCard
    {m K : ℕ} (hm : 2 ≤ m)
    (h : Real.exp (8 * (m : ℝ) + 4) <
      (K : ℝ) * Real.log K) :
    tupleLogMass K < (19 : ℝ) / 16 * Real.log K := by
  have hx : (16 : ℝ) < Real.log K := logCard_gt_sixteen hm h
  have hlogK : 0 < Real.log K := log_card_pos_of_threshold h
  have hlog16 : Real.log (16 : ℝ) < 3 := by
    have hexp3 : (16 : ℝ) < Real.exp 3 := by
      calc
        (16 : ℝ) < (27 / 10 : ℝ) ^ 3 := by norm_num
        _ < Real.exp 1 ^ 3 := by
          gcongr
          exact (by norm_num : (27 / 10 : ℝ) < 2.7182818283).trans
            Real.exp_one_gt_d9
        _ = Real.exp 3 := by simpa using (Real.exp_one_pow 3)
    exact (Real.log_lt_iff_lt_exp (by norm_num)).2 hexp3
  have hexpOne : Real.exp 1 ≤ (16 : ℝ) :=
    (Real.exp_one_lt_three.le).trans (by norm_num)
  have hratio : Real.log (Real.log K) / Real.log K ≤
      Real.log (16 : ℝ) / 16 :=
    Real.log_div_self_antitoneOn hexpOne
      (hexpOne.trans (le_of_lt hx)) (le_of_lt hx)
  have hratio' : Real.log (Real.log K) / Real.log K < (3 : ℝ) / 16 := by
    exact hratio.trans_lt
      (div_lt_div_of_pos_right hlog16 (by norm_num))
  have hloglog : Real.log (Real.log K) <
      (3 : ℝ) / 16 * Real.log K := by
    have := mul_lt_mul_of_pos_right hratio' hlogK
    field_simp [hlogK.ne'] at this
    nlinarith
  rw [tupleLogMass_eq_logCard_add_logLogCard h]
  linarith

theorem sharpDecay_mul_card_gt_thousand
    {m K : ℕ} (hm : 2 ≤ m)
    (h : Real.exp (8 * (m : ℝ) + 4) <
      (K : ℝ) * Real.log K) :
    (1000 : ℝ) < sharpDecay K * (K : ℝ) := by
  have hlogK : (16 : ℝ) < Real.log K := logCard_gt_sixteen hm h
  have hKR : (0 : ℝ) < K := by exact_mod_cast card_pos_of_threshold h
  have hexp16 : (1000 : ℝ) < Real.exp 16 := by
    calc
      (1000 : ℝ) < (2 : ℝ) ^ 16 := by norm_num
      _ < Real.exp 1 ^ 16 := by
        gcongr
        exact Real.exp_one_gt_two
      _ = Real.exp 16 := by simpa using (Real.exp_one_pow 16)
  have hKgt : (1000 : ℝ) < K :=
    hexp16.trans ((Real.lt_log_iff_exp_lt hKR).mp hlogK)
  have hA := sharpDecay_gt_thirty hm h
  nlinarith [mul_pos (by linarith [hA] : (0 : ℝ) < sharpDecay K)
    (by linarith [hKgt] : (0 : ℝ) < K)]

theorem sharp_logNumerator_lt
    {m K : ℕ} (hm : 2 ≤ m)
    (h : Real.exp (8 * (m : ℝ) + 4) <
      (K : ℝ) * Real.log K) :
    Real.log (1 + sharpDecay K * (K : ℝ)) <
      (25 : ℝ) / 24 * tupleLogMass K := by
  have hK : 0 < K := card_pos_of_threshold h
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hx : 0 < Real.log K := log_card_pos_of_threshold h
  have hL : 20 < tupleLogMass K := logMass_gt_twenty hm h
  have hLlt := tupleLogMass_lt_nineteen_sixteenths_logCard hm h
  have hAK := sharpDecay_mul_card_gt_thousand hm h
  have hfactor :
      1 + sharpDecay K * (K : ℝ) <
        (1001 : ℝ) / 1000 * (sharpDecay K * (K : ℝ)) := by
    nlinarith
  have hexpLower : (2 : ℝ) <
      Real.exp (tupleLogMass K / 24) := by
    have hfive : (2 : ℝ) < Real.exp ((5 : ℝ) / 6) := by
      have hpow : (2 : ℝ) ^ 6 <
          Real.exp ((5 : ℝ) / 6) ^ 6 := by
        rw [← Real.exp_nat_mul]
        norm_num
        calc
          (64 : ℝ) < (27 / 10 : ℝ) ^ 5 := by norm_num
          _ < Real.exp 1 ^ 5 := by
            gcongr
            exact (by norm_num : (27 / 10 : ℝ) < 2.7182818283).trans
              Real.exp_one_gt_d9
          _ = Real.exp 5 := by simpa using (Real.exp_one_pow 5)
      exact lt_of_pow_lt_pow_left₀ 6 (Real.exp_pos _).le hpow
    exact hfive.trans_le (Real.exp_monotone (by linarith [hL]))
  have hcoef :
      (1001 : ℝ) / 1000 * ((5 : ℝ) / 3 * tupleLogMass K) <
        Real.log K * 2 := by
    nlinarith
  have harg :
      1 + sharpDecay K * (K : ℝ) <
        (K : ℝ) * Real.log K *
          Real.exp (tupleLogMass K / 24) := by
    calc
      1 + sharpDecay K * (K : ℝ) <
          (1001 : ℝ) / 1000 *
            (sharpDecay K * (K : ℝ)) := hfactor
      _ = (K : ℝ) *
          ((1001 : ℝ) / 1000 *
            ((5 : ℝ) / 3 * tupleLogMass K)) := by
        unfold sharpDecay
        ring
      _ < (K : ℝ) * (Real.log K * 2) :=
        mul_lt_mul_of_pos_left hcoef hKR
      _ < (K : ℝ) * (Real.log K *
          Real.exp (tupleLogMass K / 24)) :=
        mul_lt_mul_of_pos_left
          (mul_lt_mul_of_pos_left hexpLower hx) hKR
      _ = (K : ℝ) * Real.log K *
          Real.exp (tupleLogMass K / 24) := by ring
  have hprod : 0 < (K : ℝ) * Real.log K := positive_card_log_of_threshold h
  have hexpL : Real.exp (tupleLogMass K) = (K : ℝ) * Real.log K := by
    unfold tupleLogMass
    rw [Real.exp_log hprod]
  have hrewrite :
      (K : ℝ) * Real.log K * Real.exp (tupleLogMass K / 24) =
        Real.exp ((25 : ℝ) / 24 * tupleLogMass K) := by
    rw [← hexpL, ← Real.exp_add]
    congr 1
    ring
  rw [hrewrite] at harg
  exact (Real.log_lt_iff_lt_exp (by positivity)).2 harg

theorem sharp_faceMean_lt_goodCutoff
    {m K : ℕ} (hm : 2 ≤ m)
    (h : Real.exp (8 * (m : ℝ) + 4) <
      (K : ℝ) * Real.log K) :
    ((K - 1 : ℕ) : ℝ) *
        variableCoordinateMean K (sharpDecay K) <
      sharpGoodCutoff K := by
  have hK : 0 < K := card_pos_of_threshold h
  have hA : 0 < sharpDecay K := sharpDecay_pos hm h
  have hmean0 := variableCoordinateMean_nonneg hK hA
  have hfull := sharp_fullMean_lt_seven_tenths_of_log_bounds
    hm h (sharp_logNumerator_lt hm h) (sharpDecay_mul_card_gt_thousand hm h)
  have hcast : ((K - 1 : ℕ) : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast Nat.sub_le K 1
  have hδ := sharpDelta_lt_one_twentieth hm h
  calc
    ((K - 1 : ℕ) : ℝ) *
        variableCoordinateMean K (sharpDecay K) ≤
      (K : ℝ) * variableCoordinateMean K (sharpDecay K) :=
        mul_le_mul_of_nonneg_right hcast hmean0
    _ < (63 : ℝ) / 100 := hfull
    _ < sharpGoodCutoff K := by
      unfold sharpGoodCutoff
      linarith

theorem sharp_variance_coefficient_lt
    {m K : ℕ} (hm : 2 ≤ m)
    (h : Real.exp (8 * (m : ℝ) + 4) <
      (K : ℝ) * Real.log K) :
    (12 : ℝ) * (K : ℝ) *
        (sharpDecay K * (K : ℝ))⁻¹ ^ 2 <
      (13 / sharpDecay K) *
        Erdos4.VariableMaynard.baseMass K (sharpDecay K) := by
  have hK : 0 < K := card_pos_of_threshold h
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hA : 0 < sharpDecay K := sharpDecay_pos hm h
  have hAK := sharpDecay_mul_card_gt_thousand hm h
  unfold Erdos4.VariableMaynard.baseMass
  field_simp [hA.ne', hKR.ne']
  nlinarith

theorem sharp_faceVariance_bound
    {m K : ℕ} (hm : 2 ≤ m)
    (h : Real.exp (8 * (m : ℝ) + 4) <
      (K : ℝ) * Real.log K) :
    (sharpGoodCutoff K - ((K - 1 : ℕ) : ℝ) *
        variableCoordinateMean K (sharpDecay K))⁻¹ ^ 2 *
        (((K - 1 : ℕ) : ℝ) *
          variableSecondMoment K (sharpDecay K) *
          Erdos4.VariableMaynard.baseMass K (sharpDecay K) ^ (K - 1 - 1)) <
      (1 - sharpGoodMass K) *
        Erdos4.VariableMaynard.baseMass K (sharpDecay K) ^ (K - 1) := by
  have hK2 := two_le_card_of_threshold h
  have hK : 0 < K := by omega
  have hA : 0 < sharpDecay K := sharpDecay_pos hm h
  have hmean := sharp_faceMean_lt_goodCutoff hm h
  let d := sharpGoodCutoff K - ((K - 1 : ℕ) : ℝ) *
    variableCoordinateMean K (sharpDecay K)
  have hd : (29 : ℝ) / 100 < d := by
    have hδ := sharpDelta_lt_one_twentieth hm h
    have hfull := sharp_fullMean_lt_seven_tenths_of_log_bounds
      hm h (sharp_logNumerator_lt hm h) (sharpDecay_mul_card_gt_thousand hm h)
    have hmean0 := variableCoordinateMean_nonneg hK hA
    have hcast : ((K - 1 : ℕ) : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast Nat.sub_le K 1
    have hfaceLe : ((K - 1 : ℕ) : ℝ) *
        variableCoordinateMean K (sharpDecay K) <
        (63 : ℝ) / 100 :=
      (mul_le_mul_of_nonneg_right hcast hmean0).trans_lt hfull
    dsimp [d]
    unfold sharpGoodCutoff
    linarith
  have hd0 : 0 < d := by linarith
  have hinv : d⁻¹ ^ 2 < (12 : ℝ) := by
    have hdi : d⁻¹ < (100 : ℝ) / 29 := by
      rw [inv_lt_iff_one_lt_mul₀ hd0]
      linarith
    have hdi0 : 0 ≤ d⁻¹ := inv_nonneg.mpr hd0.le
    have hs := pow_lt_pow_left₀ hdi hdi0 (by norm_num : (2 : ℕ) ≠ 0)
    nlinarith
  have hsecond := variableSecondMoment_le hK hA
  have hbase : 0 < Erdos4.VariableMaynard.baseMass K (sharpDecay K) :=
    Erdos4.VariableMaynard.baseMass_pos hK hA
  have hpow : 0 <
      Erdos4.VariableMaynard.baseMass K (sharpDecay K) ^ (K - 1 - 1) :=
    pow_pos hbase _
  have hKcast : ((K - 1 : ℕ) : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast Nat.sub_le K 1
  have hsecond0 : 0 ≤ variableSecondMoment K (sharpDecay K) := by
    unfold variableSecondMoment
    exact MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg _)
        (Erdos4.VariableMaynard.squareDensity_nonneg K (sharpDecay K) x))
  have hcoeffLe :
      ((K - 1 : ℕ) : ℝ) *
          variableSecondMoment K (sharpDecay K) ≤
        (K : ℝ) * (sharpDecay K * (K : ℝ))⁻¹ ^ 2 := by
    calc
      ((K - 1 : ℕ) : ℝ) *
          variableSecondMoment K (sharpDecay K) ≤
        (K : ℝ) * variableSecondMoment K (sharpDecay K) :=
          mul_le_mul_of_nonneg_right hKcast hsecond0
      _ ≤ (K : ℝ) * (sharpDecay K * (K : ℝ))⁻¹ ^ 2 :=
          mul_le_mul_of_nonneg_left hsecond (by exact_mod_cast hK.le)
  have hleftLe :
      d⁻¹ ^ 2 *
          (((K - 1 : ℕ) : ℝ) *
            variableSecondMoment K (sharpDecay K) *
            Erdos4.VariableMaynard.baseMass K (sharpDecay K) ^ (K - 1 - 1)) ≤
        (12 : ℝ) * ((K : ℝ) *
          (sharpDecay K * (K : ℝ))⁻¹ ^ 2 *
          Erdos4.VariableMaynard.baseMass K (sharpDecay K) ^ (K - 1 - 1)) := by
    have hrest0 : 0 ≤ ((K - 1 : ℕ) : ℝ) *
        variableSecondMoment K (sharpDecay K) *
        Erdos4.VariableMaynard.baseMass K (sharpDecay K) ^ (K - 1 - 1) := by
      positivity
    calc
      d⁻¹ ^ 2 *
          (((K - 1 : ℕ) : ℝ) *
            variableSecondMoment K (sharpDecay K) *
            Erdos4.VariableMaynard.baseMass K (sharpDecay K) ^ (K - 1 - 1)) ≤
        12 * (((K - 1 : ℕ) : ℝ) *
            variableSecondMoment K (sharpDecay K) *
            Erdos4.VariableMaynard.baseMass K (sharpDecay K) ^ (K - 1 - 1)) :=
          mul_le_mul_of_nonneg_right hinv.le hrest0
      _ ≤ 12 * ((K : ℝ) *
          (sharpDecay K * (K : ℝ))⁻¹ ^ 2 *
          Erdos4.VariableMaynard.baseMass K (sharpDecay K) ^ (K - 1 - 1)) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_right hcoeffLe hpow.le
        · norm_num
  have hcoeff := sharp_variance_coefficient_lt hm h
  have hscaled := mul_lt_mul_of_pos_right hcoeff hpow
  have hexp : K - 1 = (K - 1 - 1) + 1 := by omega
  have htarget :
      (12 : ℝ) * ((K : ℝ) *
          (sharpDecay K * (K : ℝ))⁻¹ ^ 2 *
          Erdos4.VariableMaynard.baseMass K (sharpDecay K) ^ (K - 1 - 1)) <
        (1 - sharpGoodMass K) *
          Erdos4.VariableMaynard.baseMass K (sharpDecay K) ^ (K - 1) := by
    unfold sharpGoodMass
    rw [hexp, pow_succ]
    calc
      (12 : ℝ) * ((K : ℝ) *
          (sharpDecay K * (K : ℝ))⁻¹ ^ 2 *
          Erdos4.VariableMaynard.baseMass K (sharpDecay K) ^ (K - 1 - 1)) =
        ((12 : ℝ) * (K : ℝ) *
          (sharpDecay K * (K : ℝ))⁻¹ ^ 2) *
          Erdos4.VariableMaynard.baseMass K (sharpDecay K) ^ (K - 1 - 1) := by
            ring
      _ < ((13 / sharpDecay K) *
          Erdos4.VariableMaynard.baseMass K (sharpDecay K)) *
          Erdos4.VariableMaynard.baseMass K (sharpDecay K) ^ (K - 1 - 1) :=
        hscaled
      _ = (1 - (1 - 13 / sharpDecay K)) *
          (Erdos4.VariableMaynard.baseMass K (sharpDecay K) ^
              (K - 1 - 1) *
            Erdos4.VariableMaynard.baseMass K (sharpDecay K)) := by
        ring
  change d⁻¹ ^ 2 *
        (((K - 1 : ℕ) : ℝ) *
          variableSecondMoment K (sharpDecay K) *
          Erdos4.VariableMaynard.baseMass K (sharpDecay K) ^ (K - 1 - 1)) <
      (1 - sharpGoodMass K) *
        Erdos4.VariableMaynard.baseMass K (sharpDecay K) ^ (K - 1)
  exact hleftLe.trans_lt htarget

theorem logLogCard_lt_logCard_div_sixteen_add_two
    {m K : ℕ} (hm : 2 ≤ m)
    (h : Real.exp (8 * (m : ℝ) + 4) <
      (K : ℝ) * Real.log K) :
    Real.log (Real.log K) <
      Real.log K / 16 + 2 := by
  have hx : (16 : ℝ) < Real.log K := logCard_gt_sixteen hm h
  have hx0 : 0 < Real.log K := log_card_pos_of_threshold h
  have hlog16 : Real.log (16 : ℝ) < 3 := by
    have hexp3 : (16 : ℝ) < Real.exp 3 := by
      calc
        (16 : ℝ) < (27 / 10 : ℝ) ^ 3 := by norm_num
        _ < Real.exp 1 ^ 3 := by
          gcongr
          exact (by norm_num : (27 / 10 : ℝ) < 2.7182818283).trans
            Real.exp_one_gt_d9
        _ = Real.exp 3 := by simpa using (Real.exp_one_pow 3)
    exact (Real.log_lt_iff_lt_exp (by norm_num)).2 hexp3
  have hquot : 0 < Real.log K / 16 := div_pos hx0 (by norm_num)
  have hlogquot : Real.log (Real.log K / 16) ≤
      Real.log K / 16 - 1 :=
    Real.log_le_sub_one_of_pos hquot
  have hsplit : Real.log (Real.log K) =
      Real.log (16 : ℝ) + Real.log (Real.log K / 16) := by
    rw [← Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) hquot.ne']
    congr 1
    field_simp
  rw [hsplit]
  linarith

theorem sharp_ratio_lower_gt_four_pred
    {m K : ℕ} (hm : 2 ≤ m)
    (h : Real.exp (8 * (m : ℝ) + 4) <
      (K : ℝ) * Real.log K) :
    (41 : ℝ) / 10 * ((m - 1 : ℕ) : ℝ) <
      sharpGoodMass K * Real.log K ^ 2 / sharpDecay K := by
  have hLthreshold := logMass_gt_threshold h
  have hL : 20 < tupleLogMass K := logMass_gt_twenty hm h
  have hlogK : 0 < Real.log K := log_card_pos_of_threshold h
  have hloglog := logLogCard_lt_logCard_div_sixteen_add_two hm h
  have hLexpr := tupleLogMass_eq_logCard_add_logLogCard h
  have hxLower : (16 : ℝ) / 17 * (tupleLogMass K - 2) <
      Real.log K := by
    rw [hLexpr]
    nlinarith
  have hxLower0 : 0 < (16 : ℝ) / 17 * (tupleLogMass K - 2) := by
    nlinarith
  have hsq : ((16 : ℝ) / 17 * (tupleLogMass K - 2)) ^ 2 <
      Real.log K ^ 2 :=
    pow_lt_pow_left₀ hxLower hxLower0.le (by norm_num)
  have hA : 0 < sharpDecay K := sharpDecay_pos hm h
  have hγ : 0 < sharpGoodMass K := sharpGoodMass_pos hm h
  have hfirst :
      sharpGoodMass K *
          ((16 : ℝ) / 17 * (tupleLogMass K - 2)) ^ 2 /
          sharpDecay K <
        sharpGoodMass K * Real.log K ^ 2 / sharpDecay K := by
    exact div_lt_div_of_pos_right
      (mul_lt_mul_of_pos_left hsq hγ) hA
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hpoly :
      (41 : ℝ) / 10 * ((m - 1 : ℕ) : ℝ) <
        sharpGoodMass K *
          ((16 : ℝ) / 17 * (tupleLogMass K - 2)) ^ 2 /
          sharpDecay K := by
    have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [hcast]
    unfold sharpGoodMass sharpDecay
    have hL0 : 0 < tupleLogMass K := by linarith
    field_simp [hL0.ne']
    nlinarith
  exact hpoly.trans hfirst

theorem sharp_coefficient_over_I_gt
    {m K : ℕ} (hm : 2 ≤ m)
    (h : Real.exp (8 * (m : ℝ) + 4) <
      (K : ℝ) * Real.log K) :
    (41 : ℝ) / 10 * ((m - 1 : ℕ) : ℝ) <
      (K : ℝ) *
        (variableShortMass K (sharpDecay K) (sharpDelta K) ^ 2 *
          (sharpGoodMass K *
            Erdos4.VariableMaynard.baseMass K (sharpDecay K) ^ (K - 1))) /
        BoundedGaps.Maynard.maynardI K
          (Erdos4.VariableMaynard.candidate K (sharpDecay K)) := by
  have hK2 := two_le_card_of_threshold h
  have hK : 0 < K := by omega
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hlogK : 0 < Real.log K := log_card_pos_of_threshold h
  have hA : 0 < sharpDecay K := sharpDecay_pos hm h
  have hδ : 0 < sharpDelta K := sharpDelta_pos hm h
  have hγ : 0 < sharpGoodMass K := sharpGoodMass_pos hm h
  have hL : 0 < tupleLogMass K := by
    linarith [logMass_gt_twenty hm h]
  have harg : (K : ℝ) <
      1 + sharpDecay K * (K : ℝ) * sharpDelta K := by
    unfold sharpDecay sharpDelta
    rw [show (5 : ℝ) / 3 * tupleLogMass K * (K : ℝ) *
        (tupleLogMass K)⁻¹ = (5 : ℝ) / 3 * (K : ℝ) by
      field_simp [hL.ne']]
    linarith
  have hargpos : 0 <
      1 + sharpDecay K * (K : ℝ) * sharpDelta K :=
    hKR.trans harg
  have hlogarg : Real.log K <
      Real.log (1 + sharpDecay K * (K : ℝ) * sharpDelta K) :=
    Real.strictMonoOn_log hKR hargpos harg
  have hlogarg0 : 0 < Real.log
      (1 + sharpDecay K * (K : ℝ) * sharpDelta K) :=
    hlogK.trans hlogarg
  have hsq : Real.log K ^ 2 <
      Real.log (1 + sharpDecay K * (K : ℝ) * sharpDelta K) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hlogarg)
      (add_pos hlogK hlogarg0)]
  have hfac : 1 <
      (1 + sharpDecay K * (K : ℝ)) /
        (sharpDecay K * (K : ℝ)) := by
    rw [lt_div_iff₀ (mul_pos hA hKR)]
    linarith
  have hfirst : sharpGoodMass K * Real.log K ^ 2 / sharpDecay K <
      sharpGoodMass K *
        Real.log (1 + sharpDecay K * (K : ℝ) * sharpDelta K) ^ 2 /
          sharpDecay K := by
    exact div_lt_div_of_pos_right
      (mul_lt_mul_of_pos_left hsq hγ) hA
  have hmiddle : sharpGoodMass K *
        Real.log (1 + sharpDecay K * (K : ℝ) * sharpDelta K) ^ 2 /
          sharpDecay K <
      (sharpGoodMass K *
        Real.log (1 + sharpDecay K * (K : ℝ) * sharpDelta K) ^ 2 /
          sharpDecay K) *
        ((1 + sharpDecay K * (K : ℝ)) /
          (sharpDecay K * (K : ℝ))) := by
    have hleft : 0 < sharpGoodMass K *
        Real.log (1 + sharpDecay K * (K : ℝ) * sharpDelta K) ^ 2 /
          sharpDecay K := by positivity
    nlinarith [mul_pos hleft (sub_pos.mpr hfac)]
  have heq :
      (sharpGoodMass K *
        Real.log (1 + sharpDecay K * (K : ℝ) * sharpDelta K) ^ 2 /
          sharpDecay K) *
        ((1 + sharpDecay K * (K : ℝ)) /
          (sharpDecay K * (K : ℝ))) =
      (K : ℝ) * sharpGoodMass K *
        variableShortMass K (sharpDecay K) (sharpDelta K) ^ 2 /
          Erdos4.VariableMaynard.baseMass K (sharpDecay K) := by
    rw [variableShortMass_eq hK hA hδ.le]
    unfold Erdos4.VariableMaynard.baseMass
    field_simp [hA.ne', hKR.ne']
  have hshort :
      (41 : ℝ) / 10 * ((m - 1 : ℕ) : ℝ) <
        (K : ℝ) * sharpGoodMass K *
          variableShortMass K (sharpDecay K) (sharpDelta K) ^ 2 /
            Erdos4.VariableMaynard.baseMass K (sharpDecay K) :=
    (sharp_ratio_lower_gt_four_pred hm h).trans
      (hfirst.trans (hmiddle.trans_eq heq))
  have hbase : 0 < Erdos4.VariableMaynard.baseMass K (sharpDecay K) :=
    Erdos4.VariableMaynard.baseMass_pos hK hA
  have hIpos : 0 < BoundedGaps.Maynard.maynardI K
      (Erdos4.VariableMaynard.candidate K (sharpDecay K)) :=
    Erdos4.VariableMaynard.maynardI_candidate_pos hK hA
  have hIle := Erdos4.VariableMaynard.maynardI_candidate_le hK hA
  have hpow : Erdos4.VariableMaynard.baseMass K (sharpDecay K) ^ K =
      Erdos4.VariableMaynard.baseMass K (sharpDecay K) ^ (K - 1) *
        Erdos4.VariableMaynard.baseMass K (sharpDecay K) := by
    have hexp : K = (K - 1) + 1 := by omega
    calc
      Erdos4.VariableMaynard.baseMass K (sharpDecay K) ^ K =
          Erdos4.VariableMaynard.baseMass K (sharpDecay K) ^ ((K - 1) + 1) := by
            exact congrArg (fun n : ℕ =>
              Erdos4.VariableMaynard.baseMass K (sharpDecay K) ^ n) hexp
      _ = _ := pow_succ _ _
  have hrewrite :
      (K : ℝ) * sharpGoodMass K *
          variableShortMass K (sharpDecay K) (sharpDelta K) ^ 2 /
            Erdos4.VariableMaynard.baseMass K (sharpDecay K) =
        (K : ℝ) *
          (variableShortMass K (sharpDecay K) (sharpDelta K) ^ 2 *
            (sharpGoodMass K *
              Erdos4.VariableMaynard.baseMass K (sharpDecay K) ^ (K - 1))) /
          Erdos4.VariableMaynard.baseMass K (sharpDecay K) ^ K := by
    rw [hpow]
    field_simp [hbase.ne', pow_ne_zero _ hbase.ne']
  rw [hrewrite] at hshort
  exact hshort.trans_le
    (div_le_div_of_nonneg_left (by positivity) hIpos hIle)

theorem sharp_goodFaceMass
    {m K : ℕ} (hm : 2 ≤ m)
    (h : Real.exp (8 * (m : ℝ) + 4) <
      (K : ℝ) * Real.log K)
    (J : Finset ℕ) (hcard : Fintype.card J = K - 1) :
    sharpGoodMass K *
        Erdos4.VariableMaynard.baseMass K (sharpDecay K) ^ Fintype.card J <
      ∫ t : J → ℝ in variableGoodRegion (sharpGoodCutoff K) J,
        Erdos4.VariableMaynard.productDensity K (sharpDecay K) t := by
  have hK : 0 < K := card_pos_of_threshold h
  have hA : 0 < sharpDecay K := sharpDecay_pos hm h
  have hmean := sharp_faceMean_lt_goodCutoff hm h
  have hvariance := sharp_faceVariance_bound hm h
  have hγ : 0 ≤ sharpGoodMass K := (sharpGoodMass_pos hm h).le
  have hgood := variableGoodRegion_productDensity_integral_gt_of_variance
    (K := K) (A := sharpDecay K) (q := sharpGoodCutoff K)
    (γ := sharpGoodMass K) hK hA J (by
      rw [hcard]
      exact hmean) hγ (by
      rw [hcard]
      exact hvariance)
  exact hgood

end

end MaynardTao
