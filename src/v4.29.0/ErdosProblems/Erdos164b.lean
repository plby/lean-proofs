import ErdosProblems.Erdos164

noncomputable section

namespace Strong2

/-- We index from `q ≥ 2`, since
`ArithmeticFunction.vonMangoldt 1 = 0`. -/
noncomputable def series (n : ℕ) : ℝ :=
  ∑' q : { q : ℕ // 2 ≤ q },
    ArithmeticFunction.vonMangoldt q.1 /
      ((q.1 : ℝ) * Real.log ((n * q.1 : ℕ) : ℝ) * Real.log ((2 * n * q.1 : ℕ) : ℝ))

/-- The Mellin kernel suggested by the identity
`1 / (log (nq) * log (2nq))
   = (1 / log 2) * ∫_0^∞ n^{-t} (1 - 2^{-t}) q^{-t} dt`. -/
noncomputable def kernel (n : ℕ) (t : ℝ) : ℝ :=
  ((n : ℝ) ^ (-t)) * (1 - (2 : ℝ) ^ (-t)) / Real.log (2 : ℝ)

lemma analyticSeries_bound_shift {t : ℝ} (ht : 0 < t) :
    Erdos164.analyticSeries (1 + t) ≤
      1 / t - Real.log (2 : ℝ) / Real.rpow (2 : ℝ) (1 + t) := by
  have hs : 1 < 1 + t := by linarith
  have h :=
    Erdos164.analyticSeries_add_log_term_le (s := 1 + t) hs Nat.prime_two
  have h' :
      Erdos164.analyticSeries (1 + t) +
          Real.log (2 : ℝ) / Real.rpow (2 : ℝ) (1 + t) ≤
        1 / t := by
    simpa using h
  linarith

lemma kernel_nonneg {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 0 < t) :
    0 ≤ kernel n t := by
  have hn_pos_nat : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast hn_pos_nat
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hn_factor_nonneg : 0 ≤ (n : ℝ) ^ (-t) := by
    exact (Real.rpow_pos_of_pos hn_pos _).le
  have htwo_lt_one : (2 : ℝ) ^ (-t) < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hshift_nonneg : 0 ≤ 1 - (2 : ℝ) ^ (-t) := by
    linarith
  have hnum_nonneg : 0 ≤ ((n : ℝ) ^ (-t)) * (1 - (2 : ℝ) ^ (-t)) := by
    exact mul_nonneg hn_factor_nonneg hshift_nonneg
  exact div_nonneg hnum_nonneg hlog2.le

lemma kernel_mul_analyticSeries_le
    {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 0 < t) :
    kernel n t * Erdos164.analyticSeries (1 + t) ≤
      kernel n t * (1 / t - Real.log (2 : ℝ) / Real.rpow (2 : ℝ) (1 + t)) := by
  exact mul_le_mul_of_nonneg_left (analyticSeries_bound_shift ht) (kernel_nonneg hn ht)

lemma analyticSeries_nonneg_shift (t : ℝ) :
    0 ≤ Erdos164.analyticSeries (1 + t) := by
  rw [Erdos164.analyticSeries]
  exact tsum_nonneg fun q =>
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg <|
      le_of_lt <|
        Real.rpow_pos_of_pos (by
          have hqnatpos : 0 < q.1 := lt_of_lt_of_le Nat.zero_lt_two q.2
          exact_mod_cast hqnatpos) _

lemma aux_bracket_nonneg {t : ℝ} (ht : 0 < t) :
    0 ≤ 1 / t - Real.log (2 : ℝ) / Real.rpow (2 : ℝ) (1 + t) := by
  exact (analyticSeries_nonneg_shift t).trans (analyticSeries_bound_shift ht)

lemma aux_integrand_integrable {n : ℕ} (hn : 1 < n) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ =>
        kernel n t * (1 / t - Real.log (2 : ℝ) / Real.rpow (2 : ℝ) (1 + t)))
      (Set.Ioi (0 : ℝ)) := by
  let μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
  have hn1 : 1 ≤ n := le_of_lt hn
  have hn_pos_nat : 0 < n := lt_trans Nat.zero_lt_one hn
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast hn_pos_nat
  have hn_cast : (1 : ℝ) < n := by
    exact_mod_cast hn
  have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos hn_cast
  have h_exp_int :
      MeasureTheory.Integrable
        (fun t : ℝ => Real.exp (-(Real.log (n : ℝ)) * t)) μ := by
    simpa [μ, MeasureTheory.IntegrableOn] using
      (exp_neg_integrableOn_Ioi (a := (0 : ℝ)) hlogn_pos)
  have h_meas :
      AEMeasurable
        (fun t : ℝ =>
          kernel n t * (1 / t - Real.log (2 : ℝ) / Real.rpow (2 : ℝ) (1 + t))) μ := by
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hn_pos_nat)
    have hpow_n_meas : Measurable (fun t : ℝ => (n : ℝ) ^ (-t)) :=
      ((Real.continuous_const_rpow hn0).comp (continuous_neg.comp continuous_id)).measurable
    have hpow2_neg_meas : Measurable (fun t : ℝ => (2 : ℝ) ^ (-t)) :=
      ((Real.continuous_const_rpow (by norm_num : (2 : ℝ) ≠ 0)).comp
        (continuous_neg.comp continuous_id)).measurable
    have hkernel_meas : Measurable (fun t : ℝ => kernel n t) := by
      simpa [kernel, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (hpow_n_meas.mul (measurable_const.sub hpow2_neg_meas)).mul_const
          ((Real.log (2 : ℝ))⁻¹)
    have hpow2_shift_meas : Measurable (fun t : ℝ => Real.rpow (2 : ℝ) (1 + t)) :=
      ((Real.continuous_const_rpow (by norm_num : (2 : ℝ) ≠ 0)).comp
        (continuous_const.add continuous_id)).measurable
    have hbracket_meas :
        Measurable
          (fun t : ℝ => 1 / t - Real.log (2 : ℝ) / Real.rpow (2 : ℝ) (1 + t)) := by
      exact (measurable_const.div measurable_id).sub
        (measurable_const.div hpow2_shift_meas)
    exact (hkernel_meas.mul hbracket_meas).aemeasurable
  have h_bound :
      ∀ᵐ t : ℝ ∂μ,
        ‖kernel n t * (1 / t - Real.log (2 : ℝ) / Real.rpow (2 : ℝ) (1 + t))‖ ≤
          Real.exp (-(Real.log (n : ℝ)) * t) := by
    filter_upwards [show ∀ᵐ t : ℝ ∂MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)),
        t ∈ Set.Ioi (0 : ℝ) from
          MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hcorr_nonneg :
        0 ≤ Real.log (2 : ℝ) / Real.rpow (2 : ℝ) (1 + t) := by
      exact div_nonneg hlog2.le
        (le_of_lt (Real.rpow_pos_of_pos (by norm_num) (1 + t)))
    have hB_nonneg :
        0 ≤ 1 / t - Real.log (2 : ℝ) / Real.rpow (2 : ℝ) (1 + t) :=
      aux_bracket_nonneg ht0
    have h_integrand_nonneg :
        0 ≤ kernel n t * (1 / t - Real.log (2 : ℝ) / Real.rpow (2 : ℝ) (1 + t)) := by
      exact mul_nonneg (kernel_nonneg hn1 ht0) hB_nonneg
    have hB_le : 1 / t - Real.log (2 : ℝ) / Real.rpow (2 : ℝ) (1 + t) ≤ 1 / t := by
      linarith
    have hkernel_le :
        kernel n t * (1 / t) ≤ Real.exp (-(Real.log (n : ℝ)) * t) := by
      have hn_factor_nonneg : 0 ≤ (n : ℝ) ^ (-t) := by
        exact (Real.rpow_pos_of_pos hn_pos _).le
      have hpow_pos : 0 < (2 : ℝ) ^ t := Real.rpow_pos_of_pos (by norm_num) t
      have hcoeff_le :
          (1 - (2 : ℝ) ^ (-t)) / Real.log (2 : ℝ) ≤ t := by
        have hlog :
            1 - ((2 : ℝ) ^ t)⁻¹ ≤ Real.log ((2 : ℝ) ^ t) := by
          exact Real.one_sub_inv_le_log_of_pos hpow_pos
        have hneg : (2 : ℝ) ^ (-t) = ((2 : ℝ) ^ t)⁻¹ := by
          rw [Real.rpow_neg (by norm_num : 0 ≤ (2 : ℝ))]
        have haux : 1 - (2 : ℝ) ^ (-t) ≤ t * Real.log (2 : ℝ) := by
          simpa [hneg, Real.log_rpow (by norm_num : 0 < (2 : ℝ)), mul_comm] using hlog
        rw [div_le_iff₀ hlog2]
        simpa [mul_comm, mul_left_comm, mul_assoc] using haux
      have hcoeff_mul_le_one :
          ((1 - (2 : ℝ) ^ (-t)) / Real.log (2 : ℝ)) * (1 / t) ≤ 1 := by
        calc
          ((1 - (2 : ℝ) ^ (-t)) / Real.log (2 : ℝ)) * (1 / t) ≤ t * (1 / t) := by
            gcongr
          _ = 1 := by
            field_simp [ht0.ne']
      calc
        kernel n t * (1 / t)
            = (n : ℝ) ^ (-t) * (((1 - (2 : ℝ) ^ (-t)) / Real.log (2 : ℝ)) * (1 / t)) := by
                dsimp [kernel]
                ring
        _ ≤ (n : ℝ) ^ (-t) * 1 := by
              gcongr
        _ = (n : ℝ) ^ (-t) := by ring
        _ = Real.exp (-(Real.log (n : ℝ)) * t) := by
              rw [Real.rpow_def_of_pos hn_pos]
              congr 1
              ring
    rw [Real.norm_eq_abs, abs_of_nonneg h_integrand_nonneg]
    calc
      kernel n t * (1 / t - Real.log (2 : ℝ) / Real.rpow (2 : ℝ) (1 + t))
          ≤ kernel n t * (1 / t) := by
            exact mul_le_mul_of_nonneg_left hB_le (kernel_nonneg hn1 ht0)
      _ ≤ Real.exp (-(Real.log (n : ℝ)) * t) := hkernel_le
  have h_int :
      MeasureTheory.Integrable
        (fun t : ℝ =>
          kernel n t * (1 / t - Real.log (2 : ℝ) / Real.rpow (2 : ℝ) (1 + t))) μ :=
    h_exp_int.mono' h_meas.aestronglyMeasurable h_bound
  simpa [μ, MeasureTheory.IntegrableOn] using h_int

/-- Step 1: rewrite the original series as an integral against
`Erdos164.analyticSeries (1 + t)`. -/
lemma series_eq_integral {n : ℕ} (hn : 1 ≤ n) :
    series n =
      ∫ t in Set.Ioi (0 : ℝ), kernel n t * Erdos164.analyticSeries (1 + t) := by
  classical
  let μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
  let F : {q : ℕ // 2 ≤ q} → ℝ → ℝ := fun q t =>
    kernel n t * (ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t))
  have hn_pos_nat : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast hn_pos_nat
  have hn0 : (n : ℝ) ≠ 0 := hn_pos.ne'
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hsum_analytic {t : ℝ} (ht : 0 < t) :
      Summable (fun q : {q : ℕ // 2 ≤ q} =>
        ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t)) := by
    let full : ℕ → ℝ := fun m =>
      if m = 0 then 0 else ArithmeticFunction.vonMangoldt m / Real.rpow (m : ℝ) (1 + t)
    have hLs :
        LSeriesSummable (fun m => ↑(ArithmeticFunction.vonMangoldt m)) (1 + t : ℂ) :=
      ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using add_lt_add_left ht 1)
    have hsum_full : Summable full := by
      simpa [full, LSeries.norm_term_eq, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg] using hLs.norm
    have hfull_zero :
        ∀ m ∉ Set.range (Subtype.val : {q : ℕ // 2 ≤ q} → ℕ), full m = 0 := by
      intro m hm
      have hm_lt : m < 2 := by
        by_contra h
        exact hm ⟨⟨m, not_lt.mp h⟩, rfl⟩
      interval_cases m <;> simp [full]
    have hsub : Summable (full ∘ Subtype.val) :=
      (Function.Injective.summable_iff Subtype.val_injective hfull_zero).2 hsum_full
    refine hsub.congr ?_
    intro q
    simp [full, show ((q : ℕ) ≠ 0) by omega]
  have hHas_analytic {t : ℝ} (ht : 0 < t) :
      HasSum
        (fun q : {q : ℕ // 2 ≤ q} =>
          ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t))
        (Erdos164.analyticSeries (1 + t)) := by
    simpa [Erdos164.analyticSeries] using (hsum_analytic ht).hasSum
  have hF_hasSum {t : ℝ} (ht : 0 < t) :
      HasSum (fun q : {q : ℕ // 2 ≤ q} => F q t)
        (kernel n t * Erdos164.analyticSeries (1 + t)) := by
    simpa [F, mul_assoc] using (hHas_analytic ht).mul_left (kernel n t)
  have hF_exp (q : {q : ℕ // 2 ≤ q}) (t : ℝ) :
      F q t =
        (ArithmeticFunction.vonMangoldt q.1 / ((q.1 : ℝ) * Real.log (2 : ℝ))) *
          (Real.exp (-(Real.log (((n * q.1 : ℕ) : ℝ)) * t)) -
            Real.exp (-(Real.log (((2 * n * q.1 : ℕ) : ℝ)) * t))) := by
    have hqnatpos : 0 < q.1 := lt_of_lt_of_le Nat.zero_lt_two q.2
    have hqpos : 0 < (q.1 : ℝ) := by
      exact_mod_cast hqnatpos
    have hnqpos : 0 < (((n * q.1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.mul_pos hn_pos_nat hqnatpos
    have h2nqpos : 0 < (((2 * n * q.1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.mul_pos (Nat.mul_pos (by omega) hn_pos_nat) hqnatpos
    have hq_rpow : Real.rpow (q.1 : ℝ) (1 + t) = (q.1 : ℝ) * Real.rpow (q.1 : ℝ) t := by
      simpa using (Real.rpow_add hqpos (1 : ℝ) t)
    have hnq_rpow :
        (((n * q.1 : ℕ) : ℝ)) ^ (-t) = (n : ℝ) ^ (-t) * (q.1 : ℝ) ^ (-t) := by
      simpa [Nat.cast_mul] using
        (Real.mul_rpow (show 0 ≤ (n : ℝ) by positivity)
          (show 0 ≤ (q.1 : ℝ) by positivity) (z := -t))
    have h2nq_rpow :
        (((2 * n * q.1 : ℕ) : ℝ)) ^ (-t) =
          (2 : ℝ) ^ (-t) * (n : ℝ) ^ (-t) * (q.1 : ℝ) ^ (-t) := by
      calc
        (((2 * n * q.1 : ℕ) : ℝ)) ^ (-t)
            = (2 : ℝ) ^ (-t) * (((n * q.1 : ℕ) : ℝ)) ^ (-t) := by
                simpa [Nat.cast_mul, mul_assoc] using
                  (Real.mul_rpow (show 0 ≤ (2 : ℝ) by positivity)
                    (show 0 ≤ (((n * q.1 : ℕ) : ℝ)) by positivity) (z := -t))
        _ = (2 : ℝ) ^ (-t) * ((n : ℝ) ^ (-t) * (q.1 : ℝ) ^ (-t)) := by
              rw [hnq_rpow]
        _ = (2 : ℝ) ^ (-t) * (n : ℝ) ^ (-t) * (q.1 : ℝ) ^ (-t) := by ring
    have hexp1 :
        Real.exp (-(Real.log (((n * q.1 : ℕ) : ℝ)) * t)) = (((n * q.1 : ℕ) : ℝ)) ^ (-t) := by
      rw [show -(Real.log (((n * q.1 : ℕ) : ℝ)) * t) =
          Real.log (((n * q.1 : ℕ) : ℝ)) * (-t) by ring]
      rw [← Real.rpow_def_of_pos hnqpos (-t)]
    have hexp2 :
        Real.exp (-(Real.log (((2 * n * q.1 : ℕ) : ℝ)) * t)) =
          (((2 * n * q.1 : ℕ) : ℝ)) ^ (-t) := by
      rw [show -(Real.log (((2 * n * q.1 : ℕ) : ℝ)) * t) =
          Real.log (((2 * n * q.1 : ℕ) : ℝ)) * (-t) by ring]
      rw [← Real.rpow_def_of_pos h2nqpos (-t)]
    calc
      F q t
          = kernel n t *
              (ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t)) := by
                rfl
      _ = (ArithmeticFunction.vonMangoldt q.1 / ((q.1 : ℝ) * Real.log (2 : ℝ))) *
            ((n : ℝ) ^ (-t) * (q.1 : ℝ) ^ (-t) -
              (2 : ℝ) ^ (-t) * (n : ℝ) ^ (-t) * (q.1 : ℝ) ^ (-t)) := by
              rw [kernel, hq_rpow, div_eq_mul_inv, Real.rpow_neg (le_of_lt hqpos),
                Real.rpow_eq_pow]
              field_simp [hlog2.ne', (Real.rpow_pos_of_pos hqpos t).ne']
      _ = (ArithmeticFunction.vonMangoldt q.1 / ((q.1 : ℝ) * Real.log (2 : ℝ))) *
            ((((n * q.1 : ℕ) : ℝ)) ^ (-t) - (((2 * n * q.1 : ℕ) : ℝ)) ^ (-t)) := by
              rw [hnq_rpow, h2nq_rpow]
      _ = (ArithmeticFunction.vonMangoldt q.1 / ((q.1 : ℝ) * Real.log (2 : ℝ))) *
            (Real.exp (-(Real.log (((n * q.1 : ℕ) : ℝ)) * t)) -
              Real.exp (-(Real.log (((2 * n * q.1 : ℕ) : ℝ)) * t))) := by
              rw [hexp1, hexp2]
  have hF_integrable (q : {q : ℕ // 2 ≤ q}) : MeasureTheory.Integrable (F q) μ := by
    let a : ℝ := Real.log (((n * q.1 : ℕ) : ℝ))
    let b : ℝ := Real.log (((2 * n * q.1 : ℕ) : ℝ))
    have hqnatpos : 0 < q.1 := lt_of_lt_of_le Nat.zero_lt_two q.2
    have ha_pos : 0 < a := by
      dsimp [a]
      have hgt1 : (1 : ℝ) < (((n * q.1 : ℕ) : ℝ)) := by
        exact_mod_cast lt_of_lt_of_le (by omega : 1 < q.1) (Nat.le_mul_of_pos_left q.1 hn_pos_nat)
      exact Real.log_pos hgt1
    have hb_pos : 0 < b := by
      dsimp [b]
      have hgt1 : (1 : ℝ) < (((2 * n * q.1 : ℕ) : ℝ)) := by
        exact_mod_cast lt_of_lt_of_le (by omega : 1 < q.1)
          (Nat.le_mul_of_pos_left q.1 (Nat.mul_pos (by omega) hn_pos_nat))
      exact Real.log_pos hgt1
    have hEa :
        MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-(a * t))) (Set.Ioi (0 : ℝ)) := by
      simpa [neg_mul] using (exp_neg_integrableOn_Ioi 0 ha_pos)
    have hEb :
        MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-(b * t))) (Set.Ioi (0 : ℝ)) := by
      simpa [neg_mul] using (exp_neg_integrableOn_Ioi 0 hb_pos)
    have hrepr :
        F q =
          fun t : ℝ =>
            (ArithmeticFunction.vonMangoldt q.1 / ((q.1 : ℝ) * Real.log (2 : ℝ))) *
              (Real.exp (-(a * t)) - Real.exp (-(b * t))) := by
      funext t
      dsimp [a, b]
      exact hF_exp q t
    rw [hrepr]
    simpa [μ, MeasureTheory.IntegrableOn] using (hEa.sub hEb).const_mul
      (ArithmeticFunction.vonMangoldt q.1 / ((q.1 : ℝ) * Real.log (2 : ℝ)))
  have hF_int (q : {q : ℕ // 2 ≤ q}) :
      ∫ t, F q t ∂μ =
        ArithmeticFunction.vonMangoldt q.1 /
          ((q.1 : ℝ) * Real.log (((n * q.1 : ℕ) : ℝ)) *
            Real.log (((2 * n * q.1 : ℕ) : ℝ))) := by
    let a : ℝ := Real.log (((n * q.1 : ℕ) : ℝ))
    let b : ℝ := Real.log (((2 * n * q.1 : ℕ) : ℝ))
    have hqnatpos : 0 < q.1 := lt_of_lt_of_le Nat.zero_lt_two q.2
    have hq0 : (q.1 : ℝ) ≠ 0 := by
      exact_mod_cast (show q.1 ≠ 0 by omega)
    have ha_pos : 0 < a := by
      dsimp [a]
      have hgt1 : (1 : ℝ) < (((n * q.1 : ℕ) : ℝ)) := by
        exact_mod_cast lt_of_lt_of_le (by omega : 1 < q.1) (Nat.le_mul_of_pos_left q.1 hn_pos_nat)
      exact Real.log_pos hgt1
    have hb_pos : 0 < b := by
      dsimp [b]
      have hgt1 : (1 : ℝ) < (((2 * n * q.1 : ℕ) : ℝ)) := by
        exact_mod_cast lt_of_lt_of_le (by omega : 1 < q.1)
          (Nat.le_mul_of_pos_left q.1 (Nat.mul_pos (by omega) hn_pos_nat))
      exact Real.log_pos hgt1
    have hEa :
        MeasureTheory.Integrable (fun t : ℝ => Real.exp (-(a * t))) μ := by
      simpa [μ, MeasureTheory.IntegrableOn] using (exp_neg_integrableOn_Ioi 0 ha_pos)
    have hEb :
        MeasureTheory.Integrable (fun t : ℝ => Real.exp (-(b * t))) μ := by
      simpa [μ, MeasureTheory.IntegrableOn] using (exp_neg_integrableOn_Ioi 0 hb_pos)
    have hEa_eval : ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(a * t)) = 1 / a := by
      calc
        ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(a * t))
            = a ^ (-1 / (1 : ℝ)) * Real.Gamma (1 / (1 : ℝ) + 1) := by
                simpa using (integral_exp_neg_mul_rpow (p := 1) zero_lt_one ha_pos)
        _ = 1 / a := by
              have htwo : (1 / (1 : ℝ) + 1) = 2 := by norm_num
              rw [htwo, Real.Gamma_two]
              rw [show (-1 / (1 : ℝ)) = -(1 : ℝ) by norm_num, Real.rpow_neg ha_pos.le]
              simp [one_div]
    have hEb_eval : ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(b * t)) = 1 / b := by
      calc
        ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(b * t))
            = b ^ (-1 / (1 : ℝ)) * Real.Gamma (1 / (1 : ℝ) + 1) := by
                simpa using (integral_exp_neg_mul_rpow (p := 1) zero_lt_one hb_pos)
        _ = 1 / b := by
              have htwo : (1 / (1 : ℝ) + 1) = 2 := by norm_num
              rw [htwo, Real.Gamma_two]
              rw [show (-1 / (1 : ℝ)) = -(1 : ℝ) by norm_num, Real.rpow_neg hb_pos.le]
              simp [one_div]
    have hrepr :
        F q =
          fun t : ℝ =>
            (ArithmeticFunction.vonMangoldt q.1 / ((q.1 : ℝ) * Real.log (2 : ℝ))) *
              (Real.exp (-(a * t)) - Real.exp (-(b * t))) := by
      funext t
      dsimp [a, b]
      exact hF_exp q t
    have hblog : b = Real.log (2 : ℝ) + a := by
      dsimp [a, b]
      have hnq0 : (((n * q.1 : ℕ) : ℝ)) ≠ 0 := by
        exact_mod_cast (Nat.mul_pos hn_pos_nat hqnatpos).ne'
      calc
        Real.log (((2 * n * q.1 : ℕ) : ℝ))
            = Real.log ((2 : ℝ) * (((n * q.1 : ℕ) : ℝ))) := by
                norm_num [Nat.cast_mul, mul_assoc]
        _ = Real.log (2 : ℝ) + Real.log (((n * q.1 : ℕ) : ℝ)) := by
              rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnq0]
        _ = Real.log (2 : ℝ) + a := by rfl
    have hdiff : 1 / a - 1 / b = Real.log (2 : ℝ) / (a * b) := by
      rw [hblog]
      field_simp [ha_pos.ne', hb_pos.ne', hlog2.ne']
      ring
    calc
      ∫ t, F q t ∂μ
          = (ArithmeticFunction.vonMangoldt q.1 / ((q.1 : ℝ) * Real.log (2 : ℝ))) *
              ∫ t in Set.Ioi (0 : ℝ), (Real.exp (-(a * t)) - Real.exp (-(b * t))) := by
                dsimp [μ]
                rw [hrepr, MeasureTheory.integral_const_mul]
      _ = (ArithmeticFunction.vonMangoldt q.1 / ((q.1 : ℝ) * Real.log (2 : ℝ))) *
            ((∫ t in Set.Ioi (0 : ℝ), Real.exp (-(a * t))) -
              ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(b * t))) := by
              rw [MeasureTheory.integral_sub hEa hEb]
      _ = (ArithmeticFunction.vonMangoldt q.1 / ((q.1 : ℝ) * Real.log (2 : ℝ))) *
            (1 / a - 1 / b) := by
              rw [hEa_eval, hEb_eval]
      _ = (ArithmeticFunction.vonMangoldt q.1 / ((q.1 : ℝ) * Real.log (2 : ℝ))) *
            (Real.log (2 : ℝ) / (a * b)) := by
              rw [hdiff]
      _ = ArithmeticFunction.vonMangoldt q.1 / ((q.1 : ℝ) * a * b) := by
            field_simp [hq0, ha_pos.ne', hb_pos.ne', hlog2.ne']
      _ = ArithmeticFunction.vonMangoldt q.1 /
            ((q.1 : ℝ) * Real.log (((n * q.1 : ℕ) : ℝ)) *
              Real.log (((2 * n * q.1 : ℕ) : ℝ))) := by
            rfl
  have hF_nonneg_ae (q : {q : ℕ // 2 ≤ q}) : 0 ≤ᵐ[μ] F q := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have hqnatpos : 0 < q.1 := lt_of_lt_of_le Nat.zero_lt_two q.2
    have hterm_nonneg :
        0 ≤ ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t) := by
      apply div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      exact le_of_lt (Real.rpow_pos_of_pos (by exact_mod_cast hqnatpos) _)
    dsimp [F]
    exact mul_nonneg (kernel_nonneg hn ht) hterm_nonneg
  have hnorm_int_eq (q : {q : ℕ // 2 ≤ q}) :
      ∫ t, ‖F q t‖ ∂μ =
        ArithmeticFunction.vonMangoldt q.1 /
          ((q.1 : ℝ) * Real.log (((n * q.1 : ℕ) : ℝ)) *
            Real.log (((2 * n * q.1 : ℕ) : ℝ))) := by
    calc
      ∫ t, ‖F q t‖ ∂μ = ∫ t, F q t ∂μ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [hF_nonneg_ae q] with t ht
        simp [Real.norm_of_nonneg ht]
      _ = ArithmeticFunction.vonMangoldt q.1 /
            ((q.1 : ℝ) * Real.log (((n * q.1 : ℕ) : ℝ)) *
              Real.log (((2 * n * q.1 : ℕ) : ℝ))) := hF_int q
  have hbase_scaled (q : {q : ℕ // 2 ≤ q}) :
      (n : ℝ) * Erdos164.baseFlow (n * q.1) n =
        ArithmeticFunction.vonMangoldt q.1 /
          ((q.1 : ℝ) * Real.log (((n * q.1 : ℕ) : ℝ)) ^ 2) := by
    have hqnatpos : 0 < q.1 := lt_of_lt_of_le Nat.zero_lt_two q.2
    have hq0 : (q.1 : ℝ) ≠ 0 := by
      exact_mod_cast (show q.1 ≠ 0 by omega)
    have hnq_gt1 : 1 < n * q.1 := by
      exact lt_of_lt_of_le (by omega : 1 < q.1) (Nat.le_mul_of_pos_left q.1 hn_pos_nat)
    have hdvd : n ∣ n * q.1 := by
      exact ⟨q.1, by simp⟩
    have hdiv : (n * q.1) / n = q.1 := by
      simpa [Nat.mul_comm] using Nat.mul_div_right q.1 hn_pos_nat
    by_cases hqpp : IsPrimePow q.1
    · have hbase :
          Erdos164.baseFlow (n * q.1) n =
            ArithmeticFunction.vonMangoldt q.1 /
              ((((n * q.1 : ℕ) : ℝ)) * Real.log (((n * q.1 : ℕ) : ℝ)) ^ 2) := by
        simp [Erdos164.baseFlow, hnq_gt1, hdvd, hdiv, hqpp]
      calc
        (n : ℝ) * Erdos164.baseFlow (n * q.1) n
            = (n : ℝ) *
                (ArithmeticFunction.vonMangoldt q.1 /
                  ((((n * q.1 : ℕ) : ℝ)) * Real.log (((n * q.1 : ℕ) : ℝ)) ^ 2)) := by
                    rw [hbase]
        _ = ArithmeticFunction.vonMangoldt q.1 /
              ((q.1 : ℝ) * Real.log (((n * q.1 : ℕ) : ℝ)) ^ 2) := by
              rw [Nat.cast_mul]
              field_simp [hn0, hq0]
    · have hvm : ArithmeticFunction.vonMangoldt q.1 = 0 := by
        rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
        exact hqpp
      simp [Erdos164.baseFlow, hnq_gt1, hdvd, hdiv, hqpp, hvm]
  have hterm_le_base (q : {q : ℕ // 2 ≤ q}) :
      ArithmeticFunction.vonMangoldt q.1 /
        ((q.1 : ℝ) * Real.log (((n * q.1 : ℕ) : ℝ)) *
          Real.log (((2 * n * q.1 : ℕ) : ℝ)))
      ≤ (n : ℝ) * Erdos164.baseFlow (n * q.1) n := by
    have hqnatpos : 0 < q.1 := lt_of_lt_of_le Nat.zero_lt_two q.2
    have hnum_nonneg : 0 ≤ ArithmeticFunction.vonMangoldt q.1 / (q.1 : ℝ) := by
      exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
    have hA_pos : 0 < Real.log (((n * q.1 : ℕ) : ℝ)) := by
      apply Real.log_pos
      exact_mod_cast lt_of_lt_of_le (by omega : 1 < q.1) (Nat.le_mul_of_pos_left q.1 hn_pos_nat)
    have hB_ge :
        Real.log (((n * q.1 : ℕ) : ℝ)) ≤ Real.log (((2 * n * q.1 : ℕ) : ℝ)) := by
      apply Real.log_le_log (by positivity)
      exact_mod_cast (show n * q.1 ≤ 2 * n * q.1 by
        have hle : n * q.1 ≤ 2 * (n * q.1) := Nat.le_mul_of_pos_left (n * q.1) (by omega)
        simpa [mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hle)
    have hrecip :
        1 / (Real.log (((n * q.1 : ℕ) : ℝ)) * Real.log (((2 * n * q.1 : ℕ) : ℝ))) ≤
          1 / (Real.log (((n * q.1 : ℕ) : ℝ)) ^ 2) := by
      have hden :
          Real.log (((n * q.1 : ℕ) : ℝ)) ^ 2 ≤
            Real.log (((n * q.1 : ℕ) : ℝ)) * Real.log (((2 * n * q.1 : ℕ) : ℝ)) := by
        nlinarith [hA_pos.le, hB_ge]
      exact one_div_le_one_div_of_le (by positivity) hden
    calc
      ArithmeticFunction.vonMangoldt q.1 /
          ((q.1 : ℝ) * Real.log (((n * q.1 : ℕ) : ℝ)) *
            Real.log (((2 * n * q.1 : ℕ) : ℝ)))
          =
        (ArithmeticFunction.vonMangoldt q.1 / (q.1 : ℝ)) *
          (1 /
            (Real.log (((n * q.1 : ℕ) : ℝ)) *
              Real.log (((2 * n * q.1 : ℕ) : ℝ)))) := by
                rw [div_eq_mul_inv, div_eq_mul_inv]
                ring
      _ ≤ (ArithmeticFunction.vonMangoldt q.1 / (q.1 : ℝ)) *
            (1 / (Real.log (((n * q.1 : ℕ) : ℝ)) ^ 2)) := by
              exact mul_le_mul_of_nonneg_left hrecip hnum_nonneg
      _ = (n : ℝ) * Erdos164.baseFlow (n * q.1) n := by
            rw [hbase_scaled q, div_eq_mul_inv, div_eq_mul_inv]
            ring
  let e : {q : ℕ // 2 ≤ q} → ℕ := fun q => n * q.1
  have he : Function.Injective e := by
    intro a b hab
    apply Subtype.ext
    exact Nat.mul_left_cancel hn_pos_nat hab
  have hbase_summable :
      Summable (fun q : {q : ℕ // 2 ≤ q} => (n : ℝ) * Erdos164.baseFlow (n * q.1) n) := by
    have hbasecol : Summable (fun K : ℕ => Erdos164.baseFlow K n) :=
      Erdos164.summable_baseFlow_col n
    simpa [e, Function.comp] using
      ((hbasecol.mul_left (n : ℝ)).comp_injective he)
  have hF_sum : Summable (fun q : {q : ℕ // 2 ≤ q} => ∫ t, ‖F q t‖ ∂μ) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hbase_summable
    · intro q
      exact MeasureTheory.integral_nonneg fun _ => norm_nonneg _
    · intro q
      rw [hnorm_int_eq q]
      exact hterm_le_base q
  have h_tsum_eq :
      (fun t : ℝ => ∑' q : {q : ℕ // 2 ≤ q}, F q t) =ᵐ[μ]
        fun t => kernel n t * Erdos164.analyticSeries (1 + t) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hF_hasSum ht).tsum_eq
  calc
    series n = ∑' q : {q : ℕ // 2 ≤ q}, ∫ t, F q t ∂μ := by
      unfold series
      refine tsum_congr ?_
      intro q
      exact (hF_int q).symm
    _ = ∫ t, ∑' q : {q : ℕ // 2 ≤ q}, F q t ∂μ := by
      exact MeasureTheory.integral_tsum_of_summable_integral_norm hF_integrable hF_sum
    _ = ∫ t, kernel n t * Erdos164.analyticSeries (1 + t) ∂μ := by
      exact MeasureTheory.integral_congr_ae h_tsum_eq
    _ = ∫ t in Set.Ioi (0 : ℝ), kernel n t * Erdos164.analyticSeries (1 + t) := by
      rfl

/-- Step 2: insert the existing `analyticSeries` estimate from
`B/Erdos164.lean` under the integral sign. -/
lemma series_integral_le_aux {n : ℕ} (hn : 1 < n) :
    series n ≤
      ∫ t in Set.Ioi (0 : ℝ),
        kernel n t * (1 / t - Real.log (2 : ℝ) / Real.rpow (2 : ℝ) (1 + t)) := by
  let μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
  have hn1 : 1 ≤ n := le_of_lt hn
  have h_nonneg :
      0 ≤ᵐ[μ] fun t : ℝ => kernel n t * Erdos164.analyticSeries (1 + t) := by
    filter_upwards [show ∀ᵐ t : ℝ ∂MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)),
        t ∈ Set.Ioi (0 : ℝ) from
          MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (kernel_nonneg hn1 ht) (analyticSeries_nonneg_shift t)
  have h_le :
      (fun t : ℝ => kernel n t * Erdos164.analyticSeries (1 + t)) ≤ᵐ[μ]
        (fun t : ℝ =>
          kernel n t * (1 / t - Real.log (2 : ℝ) / Real.rpow (2 : ℝ) (1 + t))) := by
    filter_upwards [show ∀ᵐ t : ℝ ∂MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)),
        t ∈ Set.Ioi (0 : ℝ) from
          MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    exact kernel_mul_analyticSeries_le hn1 ht
  rw [series_eq_integral hn1]
  simpa [μ] using
    MeasureTheory.integral_mono_of_nonneg h_nonneg (aux_integrand_integrable hn) h_le

/-- The majorant uses the positive denominator `2^t - 1`. -/
lemma two_rpow_sub_one_pos {t : ℝ} (ht : 0 < t) :
    0 < (2 : ℝ) ^ t - 1 := by
  have hpow_gt_one : 1 < (2 : ℝ) ^ t := Real.one_lt_rpow (by norm_num) ht
  linarith

/-- The key algebraic simplification: once the sharp bound
`analyticSeries (1 + t) ≤ log 2 / (2^t - 1)` is inserted, the kernel collapses
exactly to `(2n)^{-t}`. -/
lemma kernel_mul_bound_eq {n : ℕ} {t : ℝ} (ht : 0 < t) :
    kernel n t * (Real.log (2 : ℝ) / ((2 : ℝ) ^ t - 1)) =
      (((2 * n : ℕ) : ℝ) ^ (-t)) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hpow_pos : 0 < (2 : ℝ) ^ t := Real.rpow_pos_of_pos (by norm_num) t
  have hpow_ne : (2 : ℝ) ^ t ≠ 0 := hpow_pos.ne'
  have hpow_sub_ne : (2 : ℝ) ^ t - 1 ≠ 0 := (two_rpow_sub_one_pos ht).ne'
  have hratio :
      (1 - (2 : ℝ) ^ (-t)) / ((2 : ℝ) ^ t - 1) = (2 : ℝ) ^ (-t) := by
    rw [Real.rpow_neg (by norm_num : 0 ≤ (2 : ℝ))]
    field_simp [hpow_ne, hpow_sub_ne]
  calc
    kernel n t * (Real.log (2 : ℝ) / ((2 : ℝ) ^ t - 1))
        = (n : ℝ) ^ (-t) * ((1 - (2 : ℝ) ^ (-t)) / ((2 : ℝ) ^ t - 1)) := by
            rw [kernel]
            field_simp [hlog2.ne', hpow_sub_ne]
    _ = (n : ℝ) ^ (-t) * (2 : ℝ) ^ (-t) := by rw [hratio]
    _ = (2 : ℝ) ^ (-t) * (n : ℝ) ^ (-t) := by ring
    _ = (((2 * n : ℕ) : ℝ) ^ (-t)) := by
          symm
          simpa [Nat.cast_mul] using
            (Real.mul_rpow (show 0 ≤ (2 : ℝ) by positivity)
              (show 0 ≤ (n : ℝ) by positivity) (z := -t))

/-- Rewrite `(2n)^{-t}` as an exponential so that the standard integral lemma
applies. -/
lemma two_n_rpow_neg_eq_exp {n : ℕ} (hn : 1 < n) (t : ℝ) :
    (((2 * n : ℕ) : ℝ) ^ (-t)) =
      Real.exp (-(Real.log ((2 * n : ℕ) : ℝ) * t)) := by
  have htwon_pos : 0 < (((2 * n : ℕ) : ℝ)) := by
    exact_mod_cast Nat.mul_pos (by omega) (lt_trans Nat.zero_lt_one hn)
  rw [show -(Real.log ((2 * n : ℕ) : ℝ) * t) =
      Real.log ((2 * n : ℕ) : ℝ) * (-t) by ring]
  rw [← Real.rpow_def_of_pos htwon_pos (-t)]

/-- The terminal integral in the proof is absolutely integrable on `(0,∞)`. -/
lemma two_n_integrable {n : ℕ} (hn : 1 < n) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => (((2 * n : ℕ) : ℝ) ^ (-t)))
      (Set.Ioi (0 : ℝ)) := by
  have htwon_gt_one : 1 < (2 * n : ℕ) := by
    omega
  have hlog_pos : 0 < Real.log ((2 * n : ℕ) : ℝ) := by
    exact Real.log_pos (by exact_mod_cast htwon_gt_one)
  convert (exp_neg_integrableOn_Ioi (a := (0 : ℝ)) hlog_pos) using 1
  ext t
  rw [two_n_rpow_neg_eq_exp hn t, neg_mul]

/-- The last line: the integral of `(2n)^{-t}` over `(0,∞)`
is `1 / log (2n)`. -/
lemma integral_two_n_eq {n : ℕ} (hn : 1 < n) :
    ∫ t in Set.Ioi (0 : ℝ), (((2 * n : ℕ) : ℝ) ^ (-t)) =
      1 / Real.log ((2 * n : ℕ) : ℝ) := by
  have htwon_gt_one : 1 < (2 * n : ℕ) := by
    omega
  have hlog_pos : 0 < Real.log ((2 * n : ℕ) : ℝ) := by
    exact Real.log_pos (by exact_mod_cast htwon_gt_one)
  calc
    ∫ t in Set.Ioi (0 : ℝ), (((2 * n : ℕ) : ℝ) ^ (-t))
        = ∫ t in Set.Ioi (0 : ℝ),
            Real.exp (-(Real.log ((2 * n : ℕ) : ℝ) * t)) := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with t
              rw [two_n_rpow_neg_eq_exp hn t]
    _ = (Real.log ((2 * n : ℕ) : ℝ)) ^ (-1 / (1 : ℝ)) *
          Real.Gamma (1 / (1 : ℝ) + 1) := by
            simpa using
              (integral_exp_neg_mul_rpow (p := 1) zero_lt_one hlog_pos)
    _ = 1 / Real.log ((2 * n : ℕ) : ℝ) := by
          have htwo : (1 / (1 : ℝ) + 1) = 2 := by norm_num
          rw [htwo, Real.Gamma_two]
          rw [show (-1 / (1 : ℝ)) = -(1 : ℝ) by norm_num, Real.rpow_neg hlog_pos.le]
          simp [one_div]

noncomputable def etaTerm (m : ℕ) (s : ℝ) : ℝ :=
  1 / Real.rpow ((2 * m + 1 : ℕ) : ℝ) s -
    1 / Real.rpow ((2 * m + 2 : ℕ) : ℝ) s

noncomputable def etaSeries (s : ℝ) : ℝ :=
  ∑' m : ℕ, etaTerm m s

lemma zetaSeries_hasDerivAt {s : ℝ} (hs : 1 < s) :
    HasDerivAt Erdos164.zetaSeries (deriv Erdos164.zetaSeries s) s := by
  have hs' : 1 < (s : ℂ).re := by
    simpa using hs
  have hzeta_complex {x : ℝ} (hx : 1 < x) :
      ((Erdos164.zetaSeries x : ℝ) : ℂ) = LSeries 1 (x : ℂ) := by
    have hx' : 1 < (x : ℂ).re := by
      simpa using hx
    calc
      ((Erdos164.zetaSeries x : ℝ) : ℂ)
          = ∑' n : ℕ, ((1 / Real.rpow (((n + 1 : ℕ) : ℝ)) x : ℝ) : ℂ) := by
              rw [Erdos164.zetaSeries, Complex.ofReal_tsum]
      _ = ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ (x : ℂ) := by
            refine tsum_congr fun n ↦ ?_
            have hpow :
                ((((n + 1 : ℕ) : ℝ) ^ x : ℝ) : ℂ) = (↑n + 1 : ℂ) ^ (x : ℂ) := by
              simpa using (Complex.ofReal_cpow (by positivity : 0 ≤ (((n + 1 : ℕ) : ℝ))) x)
            simpa using congrArg (fun z : ℂ => (1 : ℂ) / z) hpow
      _ = riemannZeta (x : ℂ) := by
            symm
            exact zeta_eq_tsum_one_div_nat_add_one_cpow hx'
      _ = LSeries 1 (x : ℂ) := by
            symm
            exact LSeries_one_eq_riemannZeta hx'
  have hzeta_event :
      Erdos164.zetaSeries =ᶠ[nhds s] fun x : ℝ => (LSeries 1 (x : ℂ)).re := by
    refine Filter.eventuallyEq_iff_exists_mem.mpr ?_
    refine ⟨{x : ℝ | 1 < x},
      (isOpen_lt continuous_const continuous_id).mem_nhds (by simpa using hs), ?_⟩
    intro x hx
    simpa using congrArg Complex.re (hzeta_complex hx)
  have habs : LSeries.abscissaOfAbsConv 1 < (s : ℂ).re := by
    rw [LSeries.abscissaOfAbsConv_one, ← EReal.coe_one, EReal.coe_lt_coe_iff]
    simpa using hs
  have hL1_deriv :
      HasDerivAt (fun x : ℝ => (LSeries 1 (x : ℂ)).re) (deriv (LSeries 1) (s : ℂ)).re s := by
    simpa [LSeries_deriv habs] using (LSeries_hasDerivAt (f := 1) habs).real_of_complex
  have hzeta_has : HasDerivAt Erdos164.zetaSeries (deriv (LSeries 1) (s : ℂ)).re s := by
    exact hL1_deriv.congr_of_eventuallyEq hzeta_event
  have hzeta_deriv : deriv Erdos164.zetaSeries s = (deriv (LSeries 1) (s : ℂ)).re := by
    rw [Filter.EventuallyEq.deriv_eq hzeta_event]
    exact hL1_deriv.deriv
  simpa [hzeta_deriv] using hzeta_has

lemma zetaSeries_term_summable {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => 1 / Real.rpow (((n + 1 : ℕ) : ℝ)) s) := by
  have hs' : 1 < (s : ℂ).re := by
    simpa using hs
  let full : ℕ → ℝ := fun n => if n = 0 then 0 else 1 / Real.rpow ((n : ℝ)) s
  have hLs : LSeriesSummable 1 (s : ℂ) := LSeriesSummable_one_iff.mpr hs'
  have hsum_full : Summable full := by
    simpa [full, LSeries.norm_term_eq, Real.norm_eq_abs] using hLs.norm
  have hfull_zero :
      ∀ n ∉ Set.range (fun m : ℕ => m + 1), full n = 0 := by
    intro n hn
    rcases n with _ | n
    · simp [full]
    · exfalso
      exact hn ⟨n, rfl⟩
  have hsucc_inj : Function.Injective (fun n : ℕ => n + 1) := by
    intro a b h
    exact Nat.succ.inj (by simpa [Nat.succ_eq_add_one] using h)
  have hsub : Summable (full ∘ fun n : ℕ => n + 1) :=
    (Function.Injective.summable_iff hsucc_inj hfull_zero).2 hsum_full
  refine hsub.congr ?_
  intro n
  simp [full]

lemma etaSeries_eq_factor_mul_zetaSeries {s : ℝ} (hs : 1 < s) :
    etaSeries s = (1 - (2 : ℝ) ^ (1 - s)) * Erdos164.zetaSeries s := by
  let f : ℕ → ℝ := fun n => (((n + 1 : ℕ) : ℝ) ^ (-s))
  have hsum : Summable f := by
    refine (zetaSeries_term_summable hs).congr ?_
    intro n
    simpa [f, one_div] using (Real.rpow_neg (show 0 ≤ ((n + 1 : ℕ) : ℝ) by positivity) s).symm
  have htwo_inj : Function.Injective (fun n : ℕ => 2 * n) := by
    intro a b h
    have h' := congrArg (fun x : ℕ => x / 2) h
    simpa [Nat.mul_comm] using h'
  have hodd : Summable (fun n : ℕ => f (2 * n)) :=
    hsum.comp_injective htwo_inj
  have htwo_add_one_inj : Function.Injective (fun n : ℕ => 2 * n + 1) := by
    intro a b h
    have h' : 2 * a = 2 * b := by
      exact Nat.succ.inj (by simpa [Nat.succ_eq_add_one] using h)
    exact htwo_inj h'
  have heven : Summable (fun n : ℕ => f (2 * n + 1)) :=
    hsum.comp_injective htwo_add_one_inj
  have hdecomp :
      etaSeries s = (∑' n : ℕ, f (2 * n)) - ∑' n : ℕ, f (2 * n + 1) := by
    calc
      etaSeries s = ∑' n : ℕ, (f (2 * n) - f (2 * n + 1)) := by
        rw [etaSeries]
        refine tsum_congr ?_
        intro n
        calc
          etaTerm n s
              = (((2 * n + 1 : ℕ) : ℝ) ^ (-s)) - (((2 * n + 2 : ℕ) : ℝ) ^ (-s)) := by
                  rw [etaTerm]
                  rw [show 1 / Real.rpow (((2 * n + 1 : ℕ) : ℝ)) s =
                      (((2 * n + 1 : ℕ) : ℝ) ^ (-s)) by
                        symm
                        simpa [one_div] using
                          (Real.rpow_neg (show 0 ≤ (((2 * n + 1 : ℕ) : ℝ)) by positivity) s)]
                  rw [show 1 / Real.rpow (((2 * n + 2 : ℕ) : ℝ)) s =
                      (((2 * n + 2 : ℕ) : ℝ) ^ (-s)) by
                        symm
                        simpa [one_div] using
                          (Real.rpow_neg (show 0 ≤ (((2 * n + 2 : ℕ) : ℝ)) by positivity) s)]
          _ = (((2 * n + 1 : ℕ) : ℝ) ^ (-s)) - (((2 * n + 1 + 1 : ℕ) : ℝ) ^ (-s)) := by
                congr 1
          _ = f (2 * n) - f (2 * n + 1) := by
                rfl
      _ = (∑' n : ℕ, f (2 * n)) - ∑' n : ℕ, f (2 * n + 1) := by
        exact (hodd.hasSum.sub heven.hasSum).tsum_eq
  have hsplit :
      (∑' n : ℕ, f (2 * n)) + ∑' n : ℕ, f (2 * n + 1) = Erdos164.zetaSeries s := by
    calc
      (∑' n : ℕ, f (2 * n)) + ∑' n : ℕ, f (2 * n + 1) = ∑' n : ℕ, f n := by
        exact tsum_even_add_odd hodd heven
      _ = ∑' n : ℕ, 1 / Real.rpow (((n + 1 : ℕ) : ℝ)) s := by
        refine tsum_congr ?_
        intro n
        simpa [f, one_div] using (Real.rpow_neg (show 0 ≤ ((n + 1 : ℕ) : ℝ) by positivity) s)
      _ = Erdos164.zetaSeries s := by
        simp [Erdos164.zetaSeries]
  have heven_eq :
      (∑' n : ℕ, f (2 * n + 1)) = (2 : ℝ) ^ (-s) * Erdos164.zetaSeries s := by
    have hterm :
        ∀ n : ℕ, f (2 * n + 1) = (2 : ℝ) ^ (-s) * f n := by
      intro n
      have hcast_double : (2 : ℝ) * (n : ℝ) + 1 + 1 = 2 * ((n : ℝ) + 1) := by ring
      calc
        f (2 * n + 1)
            = (((2 * (n + 1 : ℕ) : ℕ) : ℝ) ^ (-s)) := by
                simp [f, hcast_double]
        _ = (2 : ℝ) ^ (-s) * (((n + 1 : ℕ) : ℝ) ^ (-s)) := by
              simpa [Nat.cast_mul] using
                (Real.mul_rpow (show 0 ≤ (2 : ℝ) by positivity)
                  (show 0 ≤ (((n + 1 : ℕ) : ℝ)) by positivity) (z := -s))
        _ = (2 : ℝ) ^ (-s) * f n := by simp [f]
    calc
      (∑' n : ℕ, f (2 * n + 1)) = ∑' n : ℕ, (2 : ℝ) ^ (-s) * f n := by
        refine tsum_congr hterm
      _ = (2 : ℝ) ^ (-s) * ∑' n : ℕ, f n := by
        rw [tsum_mul_left]
      _ = (2 : ℝ) ^ (-s) * ∑' n : ℕ, 1 / Real.rpow (((n + 1 : ℕ) : ℝ)) s := by
        refine congrArg ((2 : ℝ) ^ (-s) * ·) ?_
        refine tsum_congr ?_
        intro n
        simpa [f, one_div] using (Real.rpow_neg (show 0 ≤ ((n + 1 : ℕ) : ℝ) by positivity) s)
      _ = (2 : ℝ) ^ (-s) * Erdos164.zetaSeries s := by
        simp [Erdos164.zetaSeries]
  calc
    etaSeries s = (∑' n : ℕ, f (2 * n)) - ∑' n : ℕ, f (2 * n + 1) := hdecomp
    _ = Erdos164.zetaSeries s - 2 * (∑' n : ℕ, f (2 * n + 1)) := by
          linarith [hsplit]
    _ = Erdos164.zetaSeries s - 2 * ((2 : ℝ) ^ (-s) * Erdos164.zetaSeries s) := by
          rw [heven_eq]
    _ = (1 - (2 : ℝ) ^ (1 - s)) * Erdos164.zetaSeries s := by
          rw [show (2 : ℝ) ^ (1 - s) = 2 * (2 : ℝ) ^ (-s) by
            have htwo_pos : 0 < (2 : ℝ) := by norm_num
            calc
              (2 : ℝ) ^ (1 - s) = (2 : ℝ) ^ (1 + (-s)) := by ring_nf
              _ = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (-s) := by
                    simpa using (Real.rpow_add htwo_pos (1 : ℝ) (-s))
              _ = 2 * (2 : ℝ) ^ (-s) := by simp]
          ring

lemma log_nat_succ_div_rpow_summable {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => Real.log (n + 1) / ((n + 1 : ℝ) ^ s)) := by
  have habs : LSeries.abscissaOfAbsConv 1 < (s : ℂ).re := by
    rw [LSeries.abscissaOfAbsConv_one, ← EReal.coe_one, EReal.coe_lt_coe_iff]
    simpa using hs
  let f : ℕ → ℝ := fun n => (LSeries.term (LSeries.logMul 1) (s : ℂ) n).re
  have hsum_re : Summable f := by
    exact
      (Complex.hasSum_re (Summable.hasSum (LSeriesSummable_logMul_of_lt_re (f := 1) habs))).summable
  have htail : Summable (fun n : ℕ => f (n + 1)) := by
    exact hsum_re.comp_injective (fun a b h => Nat.succ.inj h)
  have hterm_re (n : ℕ) :
      f (n + 1) = Real.log (n + 1) / ((n + 1 : ℝ) ^ s) := by
    have hpow :
        ((((n + 1 : ℕ) : ℂ) ^ (s : ℂ))) = ((((n + 1 : ℕ) : ℝ) ^ s : ℝ) : ℂ) := by
      simpa using (Complex.ofReal_cpow (by positivity : 0 ≤ (((n + 1 : ℕ) : ℝ))) s).symm
    have hterm :
        LSeries.term (LSeries.logMul 1) (s : ℂ) (n + 1) =
          (((Real.log (n + 1) / ((n + 1 : ℝ) ^ s) : ℝ) : ℂ)) := by
      rw [LSeries.term_of_ne_zero (show n + 1 ≠ 0 by omega), LSeries.logMul, hpow]
      have hlog : Complex.log (((n + 1 : ℕ) : ℂ)) = Real.log (n + 1) := by
        simpa using (Complex.natCast_log (n := n + 1)).symm
      rw [hlog]
      simp
    simpa [f] using congrArg Complex.re hterm
  refine htail.congr ?_
  intro n
  exact hterm_re n

noncomputable def etaTermDeriv (m : ℕ) (s : ℝ) : ℝ :=
  Real.log (2 * m + 2) * (((2 * m + 2 : ℕ) : ℝ) ^ (-s)) -
    Real.log (2 * m + 1) * (((2 * m + 1 : ℕ) : ℝ) ^ (-s))

lemma etaTerm_hasDerivAt (m : ℕ) (s : ℝ) :
    HasDerivAt (etaTerm m) (etaTermDeriv m s) s := by
  have hodd_pos : 0 < (((2 * m + 1 : ℕ) : ℝ)) := by positivity
  have heven_pos : 0 < (((2 * m + 2 : ℕ) : ℝ)) := by positivity
  have hodd :
      HasDerivAt (fun x : ℝ => (((2 * m + 1 : ℕ) : ℝ) ^ (-x)))
        (-(Real.log (2 * m + 1) * (((2 * m + 1 : ℕ) : ℝ) ^ (-s)))) s := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      ((hasDerivAt_id s).neg.const_rpow hodd_pos)
  have heven :
      HasDerivAt (fun x : ℝ => (((2 * m + 2 : ℕ) : ℝ) ^ (-x)))
        (-(Real.log (2 * m + 2) * (((2 * m + 2 : ℕ) : ℝ) ^ (-s)))) s := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      ((hasDerivAt_id s).neg.const_rpow heven_pos)
  have hsub := hodd.sub heven
  convert hsub using 1
  · ext x
    unfold etaTerm
    rw [show 1 / Real.rpow (((2 * m + 1 : ℕ) : ℝ)) x = (((2 * m + 1 : ℕ) : ℝ) ^ (-x)) by
          symm
          simpa [one_div] using
            (Real.rpow_neg (show 0 ≤ (((2 * m + 1 : ℕ) : ℝ)) by positivity) x)]
    rw [show 1 / Real.rpow (((2 * m + 2 : ℕ) : ℝ)) x = (((2 * m + 2 : ℕ) : ℝ) ^ (-x)) by
          symm
          simpa [one_div] using
            (Real.rpow_neg (show 0 ≤ (((2 * m + 2 : ℕ) : ℝ)) by positivity) x)]
    rfl
  · simp [etaTermDeriv, sub_eq_add_neg, add_comm]

lemma etaSeries_summable {s : ℝ} (hs : 1 < s) :
    Summable (fun m : ℕ => etaTerm m s) := by
  let f : ℕ → ℝ := fun n => (((n + 1 : ℕ) : ℝ) ^ (-s))
  have hsum : Summable f := by
    refine (zetaSeries_term_summable hs).congr ?_
    intro n
    simpa [f, one_div] using (Real.rpow_neg (show 0 ≤ ((n + 1 : ℕ) : ℝ) by positivity) s).symm
  have htwo_inj : Function.Injective (fun n : ℕ => 2 * n) := by
    intro a b h
    have h' := congrArg (fun x : ℕ => x / 2) h
    simpa [Nat.mul_comm] using h'
  have htwo_add_one_inj : Function.Injective (fun n : ℕ => 2 * n + 1) := by
    intro a b h
    have h' : 2 * a = 2 * b := by
      simpa [Nat.succ_eq_add_one] using congrArg Nat.pred h
    exact htwo_inj h'
  have hodd : Summable (fun n : ℕ => f (2 * n)) :=
    hsum.comp_injective htwo_inj
  have heven : Summable (fun n : ℕ => f (2 * n + 1)) :=
    hsum.comp_injective htwo_add_one_inj
  have hcongr :
      (fun m : ℕ => etaTerm m s) = fun n : ℕ => f (2 * n) - f (2 * n + 1) := by
    funext n
    calc
      etaTerm n s
          = (((2 * n + 1 : ℕ) : ℝ) ^ (-s)) - (((2 * n + 2 : ℕ) : ℝ) ^ (-s)) := by
              rw [etaTerm]
              rw [show 1 / Real.rpow (((2 * n + 1 : ℕ) : ℝ)) s =
                  (((2 * n + 1 : ℕ) : ℝ) ^ (-s)) by
                    symm
                    simpa [one_div] using
                      (Real.rpow_neg (show 0 ≤ (((2 * n + 1 : ℕ) : ℝ)) by positivity) s)]
              rw [show 1 / Real.rpow (((2 * n + 2 : ℕ) : ℝ)) s =
                  (((2 * n + 2 : ℕ) : ℝ) ^ (-s)) by
                    symm
                    simpa [one_div] using
                      (Real.rpow_neg (show 0 ≤ (((2 * n + 2 : ℕ) : ℝ)) by positivity) s)]
      _ = (((2 * n + 1 : ℕ) : ℝ) ^ (-s)) - (((2 * n + 1 + 1 : ℕ) : ℝ) ^ (-s)) := by
            congr 1
      _ = f (2 * n) - f (2 * n + 1) := by
            rfl
  rw [hcongr]
  exact (hodd.hasSum.sub heven.hasSum).summable

lemma etaSeries_hasDerivAt {s : ℝ} (hs : 1 < s) :
    HasDerivAt etaSeries (∑' m : ℕ, etaTermDeriv m s) s := by
  let c : ℝ := (1 + s) / 2
  have hc : 1 < c := by
    dsimp [c]
    linarith
  have hs_mem : s ∈ Set.Ioi c := by
    change c < s
    dsimp [c]
    linarith
  let g : ℕ → ℝ := fun n => Real.log (n + 1) * (((n + 1 : ℕ) : ℝ) ^ (-c))
  have hsumg : Summable g := by
    refine (log_nat_succ_div_rpow_summable hc).congr ?_
    intro n
    simpa [g, div_eq_mul_inv] using
      congrArg (fun t : ℝ => Real.log (n + 1) * t)
        ((Real.rpow_neg (show 0 ≤ ((n + 1 : ℕ) : ℝ) by positivity) c).symm)
  have htwo_inj : Function.Injective (fun n : ℕ => 2 * n) := by
    intro a b h
    have h' := congrArg (fun x : ℕ => x / 2) h
    simpa [Nat.mul_comm] using h'
  have htwo_add_one_inj : Function.Injective (fun n : ℕ => 2 * n + 1) := by
    intro a b h
    have h' : 2 * a = 2 * b := by
      simpa [Nat.succ_eq_add_one] using congrArg Nat.pred h
    exact htwo_inj h'
  let u : ℕ → ℝ := fun m => g (2 * m) + g (2 * m + 1)
  have hu : Summable u := by
    dsimp [u]
    exact (hsumg.comp_injective htwo_inj).add (hsumg.comp_injective htwo_add_one_inj)
  refine hasDerivAt_tsum_of_isPreconnected (u := u) hu isOpen_Ioi isPreconnected_Ioi ?_ ?_
    hs_mem (etaSeries_summable hs) hs_mem
  · intro m y hy
    exact etaTerm_hasDerivAt m y
  · intro m y hy
    have hyc : c < y := hy
    have hodd_pos : 0 < (((2 * m + 1 : ℕ) : ℝ)) := by positivity
    have heven_pos : 0 < (((2 * m + 2 : ℕ) : ℝ)) := by positivity
    have hodd_one_le' : (1 : ℝ) ≤ (((2 * m + 1 : ℕ) : ℝ)) := by
      have hnat : 1 ≤ 2 * m + 1 := by omega
      exact_mod_cast hnat
    have heven_one_le' : (1 : ℝ) ≤ (((2 * m + 2 : ℕ) : ℝ)) := by
      have hnat : 1 ≤ 2 * m + 2 := by omega
      exact_mod_cast hnat
    have hodd_log_nonneg : 0 ≤ Real.log (2 * m + 1) := by
      have hcast_odd : (((2 * m + 1 : ℕ) : ℝ)) = 2 * (m : ℝ) + 1 := by
        norm_num [Nat.cast_add, Nat.cast_mul, mul_comm]
      rw [hcast_odd] at hodd_one_le'
      have hodd_one_le : (1 : ℝ) ≤ 2 * (m : ℝ) + 1 := by
        exact hodd_one_le'
      exact Real.log_nonneg hodd_one_le
    have heven_log_nonneg : 0 ≤ Real.log (2 * m + 2) := by
      have hcast_even : (((2 * m + 2 : ℕ) : ℝ)) = 2 * (m : ℝ) + 2 := by
        norm_num [Nat.cast_add, Nat.cast_mul, mul_comm]
      rw [hcast_even] at heven_one_le'
      have heven_one_le : (1 : ℝ) ≤ 2 * (m : ℝ) + 2 := by
        exact heven_one_le'
      exact Real.log_nonneg heven_one_le
    have hodd_rpow :
        (((2 * m + 1 : ℕ) : ℝ) ^ (-y)) ≤ (((2 * m + 1 : ℕ) : ℝ) ^ (-c)) := by
      exact Real.rpow_le_rpow_of_exponent_le hodd_one_le'
        (by linarith)
    have heven_rpow :
        (((2 * m + 2 : ℕ) : ℝ) ^ (-y)) ≤ (((2 * m + 2 : ℕ) : ℝ) ^ (-c)) := by
      exact Real.rpow_le_rpow_of_exponent_le heven_one_le'
        (by linarith)
    calc
      ‖etaTermDeriv m y‖
          ≤ ‖Real.log (2 * m + 2) * (((2 * m + 2 : ℕ) : ℝ) ^ (-y))‖ +
              ‖Real.log (2 * m + 1) * (((2 * m + 1 : ℕ) : ℝ) ^ (-y))‖ := by
                simpa [etaTermDeriv, sub_eq_add_neg] using
                  (norm_sub_le (Real.log (2 * m + 2) * (((2 * m + 2 : ℕ) : ℝ) ^ (-y)))
                    (Real.log (2 * m + 1) * (((2 * m + 1 : ℕ) : ℝ) ^ (-y))))
      _ = Real.log (2 * m + 2) * (((2 * m + 2 : ℕ) : ℝ) ^ (-y)) +
            Real.log (2 * m + 1) * (((2 * m + 1 : ℕ) : ℝ) ^ (-y)) := by
              rw [Real.norm_of_nonneg (mul_nonneg heven_log_nonneg (by positivity))]
              rw [Real.norm_of_nonneg (mul_nonneg hodd_log_nonneg (by positivity))]
      _ ≤ Real.log (2 * m + 2) * (((2 * m + 2 : ℕ) : ℝ) ^ (-c)) +
            Real.log (2 * m + 1) * (((2 * m + 1 : ℕ) : ℝ) ^ (-c)) := by
              gcongr
      _ = u m := by
            dsimp [u, g]
            have h0 : (((2 * m : ℕ) : ℝ) + 1) = (((2 * m + 1 : ℕ) : ℝ)) := by
              norm_num [Nat.cast_add, Nat.cast_mul, mul_comm]
            have h1 : (((2 * m + 1 : ℕ) : ℝ) + 1) = (((2 * m + 2 : ℕ) : ℝ)) := by
              have hleft : (((2 * m + 1 : ℕ) : ℝ) + 1) = (m : ℝ) * 2 + 1 + 1 := by
                norm_num [Nat.cast_add, Nat.cast_mul, mul_comm]
              have hmid : (m : ℝ) * 2 + 1 + 1 = (m : ℝ) * 2 + 2 := by ring
              have hright : (((2 * m + 2 : ℕ) : ℝ)) = (m : ℝ) * 2 + 2 := by
                norm_num [Nat.cast_add, Nat.cast_mul, mul_comm]
              rw [hleft, hmid, hright]
            rw [h0, h1]
            have h2 : (((2 * m + 1 + 1 : ℕ) : ℝ)) = (((2 * m + 2 : ℕ) : ℝ)) := by
              norm_num [Nat.cast_add, Nat.cast_mul, mul_comm]
              ring
            rw [h2]
            norm_num [Nat.cast_add, Nat.cast_mul, mul_comm]
            rw [add_comm]

lemma hasDerivAt_log_const_div_rpow (a u : ℝ) (ha : 0 < a) :
    HasDerivAt (fun s : ℝ => Real.log a / a ^ s) (-(Real.log a) ^ 2 / a ^ u) u := by
  have hpow :
      HasDerivAt (fun s : ℝ => a ^ (-s)) (-(Real.log a * a ^ (-u))) u := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      ((hasDerivAt_id u).neg.const_rpow ha)
  have h := hpow.const_mul (Real.log a)
  convert h using 1
  · ext s
    rw [div_eq_mul_inv, Real.rpow_neg ha.le]
  · rw [div_eq_mul_inv, Real.rpow_neg ha.le]
    ring

lemma first_eta_deriv_block_nonneg {s : ℝ} (hs : 1 < s) :
    0 ≤
      Real.log (2 : ℝ) / ((2 : ℝ) ^ s) - Real.log (3 : ℝ) / ((3 : ℝ) ^ s) +
        Real.log (4 : ℝ) / ((4 : ℝ) ^ s) - Real.log (5 : ℝ) / ((5 : ℝ) ^ s) := by
  have hs_ge_one : (1 : ℝ) ≤ s := by linarith
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hfive :
      Real.log (5 : ℝ) / (5 : ℝ) ^ s ≤
        ((3 / 5 : ℝ) * Real.log (5 : ℝ)) / (3 : ℝ) ^ s := by
    have hratio : (5 / 3 : ℝ) ≤ (5 / 3 : ℝ) ^ s := by
      simpa using
        (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 5 / 3) hs_ge_one)
    have hdiv :
        (5 / 3 : ℝ) ^ s = (5 : ℝ) ^ s / (3 : ℝ) ^ s := by
      simpa using
        (Real.div_rpow (show 0 ≤ (5 : ℝ) by positivity)
          (show 0 ≤ (3 : ℝ) by positivity) s)
    have h3pow_pos : 0 < (3 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
    have h5pow_pos : 0 < (5 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
    have hpow : (5 / 3 : ℝ) * (3 : ℝ) ^ s ≤ (5 : ℝ) ^ s := by
      rw [hdiv] at hratio
      exact (le_div_iff₀ h3pow_pos).mp hratio
    have hcross :
        Real.log (5 : ℝ) * (3 : ℝ) ^ s ≤
          ((3 / 5 : ℝ) * Real.log (5 : ℝ)) * (5 : ℝ) ^ s := by
      have hlog5_nonneg : 0 ≤ Real.log (5 : ℝ) := Real.log_nonneg (by norm_num)
      nlinarith
    exact (div_le_div_iff₀ h5pow_pos h3pow_pos).2 hcross
  have hgeom : 3 ≤ (3 / 2 : ℝ) ^ s + 2 * (3 / 4 : ℝ) ^ s := by
    have hprod :
        (9 / 8 : ℝ) ≤ (3 / 2 : ℝ) ^ s * (3 / 4 : ℝ) ^ s := by
      calc
        (9 / 8 : ℝ) ≤ (9 / 8 : ℝ) ^ s := by
          simpa using
            (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 9 / 8) hs_ge_one)
        _ = (3 / 2 : ℝ) ^ s * (3 / 4 : ℝ) ^ s := by
            simpa [show (9 / 8 : ℝ) = (3 / 2 : ℝ) * (3 / 4 : ℝ) by norm_num] using
              (Real.mul_rpow (show 0 ≤ (3 / 2 : ℝ) by positivity)
                (show 0 ≤ (3 / 4 : ℝ) by positivity) (z := s))
    have hsquare : 9 ≤ ((3 / 2 : ℝ) ^ s + 2 * (3 / 4 : ℝ) ^ s) ^ 2 := by
      have hsq_nonneg : 0 ≤ ((3 / 2 : ℝ) ^ s - 2 * (3 / 4 : ℝ) ^ s) ^ 2 := sq_nonneg _
      nlinarith
    have hnonneg : 0 ≤ (3 / 2 : ℝ) ^ s + 2 * (3 / 4 : ℝ) ^ s := by positivity
    nlinarith
  have hlog_bound :
      Real.log (3 : ℝ) + (3 / 5 : ℝ) * Real.log (5 : ℝ) ≤ 3 * Real.log (2 : ℝ) := by
    have hpow :
        ((3 : ℝ) ^ (5 : ℝ)) * ((5 : ℝ) ^ (3 : ℝ)) ≤ (8 : ℝ) ^ (5 : ℝ) := by
      norm_num [Real.rpow_natCast]
    have hlog :
        Real.log (((3 : ℝ) ^ (5 : ℝ)) * ((5 : ℝ) ^ (3 : ℝ))) ≤
          Real.log ((8 : ℝ) ^ (5 : ℝ)) := by
      exact Real.log_le_log (by positivity) hpow
    rw [Real.log_mul (by positivity) (by positivity)] at hlog
    rw [Real.log_rpow (by norm_num : 0 < (3 : ℝ)),
      Real.log_rpow (by norm_num : 0 < (5 : ℝ)),
      Real.log_rpow (by norm_num : 0 < (8 : ℝ))] at hlog
    have hlog8 : Real.log (8 : ℝ) = 3 * Real.log (2 : ℝ) := by
      rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) by norm_num [Real.rpow_natCast],
        Real.log_rpow (by norm_num : 0 < (2 : ℝ))]
    rw [hlog8] at hlog
    nlinarith
  have hmain :
      Real.log (3 : ℝ) / (3 : ℝ) ^ s + Real.log (5 : ℝ) / (5 : ℝ) ^ s ≤
        Real.log (2 : ℝ) / (2 : ℝ) ^ s + Real.log (4 : ℝ) / (4 : ℝ) ^ s := by
    have h3pow_pos : 0 < (3 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
    have hlhs :
        Real.log (3 : ℝ) / (3 : ℝ) ^ s + Real.log (5 : ℝ) / (5 : ℝ) ^ s ≤
          (Real.log (3 : ℝ) + (3 / 5 : ℝ) * Real.log (5 : ℝ)) / (3 : ℝ) ^ s := by
      calc
        Real.log (3 : ℝ) / (3 : ℝ) ^ s + Real.log (5 : ℝ) / (5 : ℝ) ^ s
            ≤ Real.log (3 : ℝ) / (3 : ℝ) ^ s +
                ((3 / 5 : ℝ) * Real.log (5 : ℝ)) / (3 : ℝ) ^ s := by
                  exact add_le_add_right hfive _
        _ = (Real.log (3 : ℝ) + (3 / 5 : ℝ) * Real.log (5 : ℝ)) / (3 : ℝ) ^ s := by
              rw [add_div]
    have hlog_div :
        (Real.log (3 : ℝ) + (3 / 5 : ℝ) * Real.log (5 : ℝ)) / (3 : ℝ) ^ s ≤
          (3 * Real.log (2 : ℝ)) / (3 : ℝ) ^ s := by
      exact (div_le_div_iff_of_pos_right h3pow_pos).2 hlog_bound
    have hrhs :
        (3 * Real.log (2 : ℝ)) / (3 : ℝ) ^ s ≤
          Real.log (2 : ℝ) / (2 : ℝ) ^ s + Real.log (4 : ℝ) / (4 : ℝ) ^ s := by
      have hlog :
          3 * Real.log (2 : ℝ) ≤
            ((3 / 2 : ℝ) ^ s + 2 * (3 / 4 : ℝ) ^ s) * Real.log (2 : ℝ) := by
        nlinarith [hgeom, hlog2]
      have hdiv :
          (3 * Real.log (2 : ℝ)) / (3 : ℝ) ^ s ≤
            (((3 / 2 : ℝ) ^ s + 2 * (3 / 4 : ℝ) ^ s) * Real.log (2 : ℝ)) / (3 : ℝ) ^ s := by
        exact (div_le_div_iff_of_pos_right h3pow_pos).2 hlog
      have h32 :
          ((3 / 2 : ℝ) ^ s * Real.log (2 : ℝ)) / (3 : ℝ) ^ s =
            Real.log (2 : ℝ) / (2 : ℝ) ^ s := by
        rw [show (3 / 2 : ℝ) ^ s = (3 : ℝ) ^ s / (2 : ℝ) ^ s by
          simpa using
            (Real.div_rpow (show 0 ≤ (3 : ℝ) by positivity)
              (show 0 ≤ (2 : ℝ) by positivity) s)]
        field_simp [show (3 : ℝ) ^ s ≠ 0 by positivity, show (2 : ℝ) ^ s ≠ 0 by positivity]
      have h34 :
          (2 * (3 / 4 : ℝ) ^ s * Real.log (2 : ℝ)) / (3 : ℝ) ^ s =
            Real.log (4 : ℝ) / (4 : ℝ) ^ s := by
        rw [show (3 / 4 : ℝ) ^ s = (3 : ℝ) ^ s / (4 : ℝ) ^ s by
          simpa using
            (Real.div_rpow (show 0 ≤ (3 : ℝ) by positivity)
              (show 0 ≤ (4 : ℝ) by positivity) s)]
        rw [show Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) by
          rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num [Real.rpow_natCast],
            Real.log_rpow (by norm_num : 0 < (2 : ℝ))]]
        field_simp [show (3 : ℝ) ^ s ≠ 0 by positivity, show (4 : ℝ) ^ s ≠ 0 by positivity]
      calc
        (3 * Real.log (2 : ℝ)) / (3 : ℝ) ^ s
            ≤ (((3 / 2 : ℝ) ^ s + 2 * (3 / 4 : ℝ) ^ s) * Real.log (2 : ℝ)) / (3 : ℝ) ^ s := hdiv
        _ = ((3 / 2 : ℝ) ^ s * Real.log (2 : ℝ)) / (3 : ℝ) ^ s +
              (2 * (3 / 4 : ℝ) ^ s * Real.log (2 : ℝ)) / (3 : ℝ) ^ s := by
                rw [add_mul, add_div]
        _ = Real.log (2 : ℝ) / (2 : ℝ) ^ s + Real.log (4 : ℝ) / (4 : ℝ) ^ s := by
              rw [h32, h34]
    exact hlhs.trans (hlog_div.trans hrhs)
  nlinarith [hmain]

lemma etaSeries_deriv_eq_pair_tsum {s : ℝ} (hs : 1 < s) :
    deriv etaSeries s =
      ∑' m : ℕ,
        (Real.log (2 * m + 2) / (((2 * m + 2 : ℕ) : ℝ) ^ s) -
          Real.log (2 * m + 3) / (((2 * m + 3 : ℕ) : ℝ) ^ s)) := by
  let f : ℕ → ℝ := fun n => Real.log (n + 1) / ((n + 1 : ℝ) ^ s)
  have hsum : Summable f := log_nat_succ_div_rpow_summable hs
  have htwo_inj : Function.Injective (fun n : ℕ => 2 * n) := by
    intro a b h
    have h' := congrArg (fun x : ℕ => x / 2) h
    simpa [Nat.mul_comm] using h'
  have hodd_inj : Function.Injective (fun n : ℕ => 2 * n + 1) := by
    intro a b h
    have h' : 2 * a = 2 * b := by
      simpa [Nat.succ_eq_add_one] using congrArg Nat.pred h
    exact htwo_inj h'
  have hshift_inj : Function.Injective (fun n : ℕ => 2 * n + 2) := by
    intro a b h
    have h' : 2 * a = 2 * b := by
      simpa [Nat.succ_eq_add_one] using congrArg Nat.pred (congrArg Nat.pred h)
    exact htwo_inj h'
  have heven : Summable (fun n : ℕ => f (2 * n)) := hsum.comp_injective htwo_inj
  have hodd : Summable (fun n : ℕ => f (2 * n + 1)) := hsum.comp_injective hodd_inj
  have hshift : Summable (fun n : ℕ => f (2 * n + 2)) := hsum.comp_injective hshift_inj
  have hderiv0 :
      deriv etaSeries s = ∑' m : ℕ, (f (2 * m + 1) - f (2 * m)) := by
    rw [(etaSeries_hasDerivAt hs).deriv]
    refine tsum_congr ?_
    intro m
    calc
      etaTermDeriv m s
          = Real.log (2 * m + 2) / (((2 * m + 2 : ℕ) : ℝ) ^ s) -
              Real.log (2 * m + 1) / (((2 * m + 1 : ℕ) : ℝ) ^ s) := by
                rw [etaTermDeriv]
                rw [show (((2 * m + 2 : ℕ) : ℝ) ^ (-s)) =
                    ((((2 * m + 2 : ℕ) : ℝ) ^ s)⁻¹) by
                      rw [Real.rpow_neg (show 0 ≤ (((2 * m + 2 : ℕ) : ℝ)) by positivity)]]
                rw [show (((2 * m + 1 : ℕ) : ℝ) ^ (-s)) =
                    ((((2 * m + 1 : ℕ) : ℝ) ^ s)⁻¹) by
                      rw [Real.rpow_neg (show 0 ≤ (((2 * m + 1 : ℕ) : ℝ)) by positivity)]]
                simp [div_eq_mul_inv]
      _ = f (2 * m + 1) - f (2 * m) := by
            dsimp [f]
            rw [show (((2 * m + 1 : ℕ) : ℝ) + 1) = 2 * (m : ℝ) + 2 by
              norm_num [Nat.cast_add, Nat.cast_mul, mul_comm]
              try ring]
            rw [show (((2 * m : ℕ) : ℝ) + 1) = 2 * (m : ℝ) + 1 by
              norm_num [Nat.cast_add, Nat.cast_mul, mul_comm]
              try ring]
            rw [show (((2 * m + 2 : ℕ) : ℝ)) = 2 * (m : ℝ) + 2 by
              norm_num [Nat.cast_add, Nat.cast_mul, mul_comm]
              try ring]
            rw [show (((2 * m + 1 : ℕ) : ℝ)) = 2 * (m : ℝ) + 1 by
              norm_num [Nat.cast_add, Nat.cast_mul, mul_comm]
              try ring]
  have heven_shift :
      (∑' n : ℕ, f (2 * n)) = ∑' n : ℕ, f (2 * n + 2) := by
    let g : ℕ → ℝ := fun n => f (2 * n)
    have hg : Summable g := heven
    have hg0 : g 0 = 0 := by
      dsimp [g, f]
      simp
    calc
      ∑' n : ℕ, f (2 * n) = ∑' n : ℕ, g n := by rfl
      _ = ∑ i ∈ Finset.range 1, g i + ∑' n : ℕ, g (n + 1) := by
            exact (hg.sum_add_tsum_nat_add 1).symm
      _ = ∑' n : ℕ, g (n + 1) := by simp [hg0]
      _ = ∑' n : ℕ, f (2 * n + 2) := by
            refine tsum_congr ?_
            intro n
            simp [g, Nat.mul_add, add_comm]
  calc
    deriv etaSeries s = ∑' m : ℕ, (f (2 * m + 1) - f (2 * m)) := hderiv0
    _ = (∑' m : ℕ, f (2 * m + 1)) - ∑' m : ℕ, f (2 * m) := by
          exact (hodd.hasSum.sub heven.hasSum).tsum_eq
    _ = (∑' m : ℕ, f (2 * m + 1)) - ∑' m : ℕ, f (2 * m + 2) := by
          rw [heven_shift]
    _ = ∑' m : ℕ, (f (2 * m + 1) - f (2 * m + 2)) := by
          symm
          exact (hodd.hasSum.sub hshift.hasSum).tsum_eq
    _ = ∑' m : ℕ,
          (Real.log (2 * m + 2) / (((2 * m + 2 : ℕ) : ℝ) ^ s) -
            Real.log (2 * m + 3) / (((2 * m + 3 : ℕ) : ℝ) ^ s)) := by
          refine tsum_congr ?_
          intro m
          dsimp [f]
          rw [show (((2 * m + 1 : ℕ) : ℝ) + 1) = 2 * (m : ℝ) + 2 by
            norm_num [Nat.cast_add, Nat.cast_mul, mul_comm]
            try ring]
          rw [show (((2 * m + 2 : ℕ) : ℝ) + 1) = 2 * (m : ℝ) + 3 by
            norm_num [Nat.cast_add, Nat.cast_mul, mul_comm]
            try ring]
          rw [show (((2 * m + 2 : ℕ) : ℝ)) = 2 * (m : ℝ) + 2 by
            norm_num [Nat.cast_add, Nat.cast_mul, mul_comm]
            try ring]
          rw [show (((2 * m + 3 : ℕ) : ℝ)) = 2 * (m : ℝ) + 3 by
            norm_num [Nat.cast_add, Nat.cast_mul, mul_comm]
            try ring]

lemma eta_deriv_pair_nonneg {s : ℝ} (hs : 1 < s) {m : ℕ} (hm : 1 ≤ m) :
    0 ≤
      Real.log (2 * m + 2) / (((2 * m + 2 : ℕ) : ℝ) ^ s) -
        Real.log (2 * m + 3) / (((2 * m + 3 : ℕ) : ℝ) ^ s) := by
  have hs_pos : 0 < s := by linarith
  have hinv_lt_one : 1 / s < (1 : ℝ) := by
    simpa using (one_div_lt_one_div_of_lt (show (0 : ℝ) < 1 by norm_num) hs)
  have hexp_lt_four : Real.exp (1 / s) < (4 : ℝ) := by
    have hexp_lt_three : Real.exp (1 / s) < (3 : ℝ) := by
      exact lt_trans (Real.exp_lt_exp.mpr hinv_lt_one) Real.exp_one_lt_three
    linarith
  have hanti := Real.log_div_self_rpow_antitoneOn hs_pos
  have hmem₁ : (2 * m + 2 : ℝ) ∈ {x : ℝ | Real.exp (1 / s) ≤ x} := by
    have h4le : (4 : ℝ) ≤ (2 * m + 2 : ℝ) := by
      exact_mod_cast (show 4 ≤ 2 * m + 2 by omega)
    exact le_trans hexp_lt_four.le h4le
  have hmem₂ : (2 * m + 3 : ℝ) ∈ {x : ℝ | Real.exp (1 / s) ≤ x} := by
    have h4le : (4 : ℝ) ≤ (2 * m + 3 : ℝ) := by
      exact_mod_cast (show 4 ≤ 2 * m + 3 by omega)
    exact le_trans hexp_lt_four.le h4le
  have hle : (2 * m + 2 : ℝ) ≤ 2 * m + 3 := by linarith
  have hcmp :
      Real.log (2 * m + 3) / (((2 * m + 3 : ℕ) : ℝ) ^ s) ≤
        Real.log (2 * m + 2) / (((2 * m + 2 : ℕ) : ℝ) ^ s) := by
    simpa [Nat.cast_add, Nat.cast_mul, mul_comm] using hanti hmem₁ hmem₂ hle
  exact sub_nonneg.mpr hcmp

lemma etaSeries_deriv_nonneg {s : ℝ} (hs : 1 < s) :
    0 ≤ deriv etaSeries s := by
  let pair : ℕ → ℝ := fun m =>
    Real.log (2 * m + 2) / (((2 * m + 2 : ℕ) : ℝ) ^ s) -
      Real.log (2 * m + 3) / (((2 * m + 3 : ℕ) : ℝ) ^ s)
  have hderiv : deriv etaSeries s = ∑' m : ℕ, pair m := by
    simpa [pair] using etaSeries_deriv_eq_pair_tsum hs
  let f : ℕ → ℝ := fun n => Real.log (n + 1) / ((n + 1 : ℝ) ^ s)
  have hsum : Summable f := log_nat_succ_div_rpow_summable hs
  have hodd_inj : Function.Injective (fun n : ℕ => 2 * n + 1) := by
    intro a b h
    have h' : 2 * a = 2 * b := by
      simpa [Nat.succ_eq_add_one] using congrArg Nat.pred h
    have h'' := congrArg (fun x : ℕ => x / 2) h'
    simpa [Nat.mul_comm] using h''
  have hshift_inj : Function.Injective (fun n : ℕ => 2 * n + 2) := by
    intro a b h
    have h' : 2 * a = 2 * b := by
      simpa [Nat.succ_eq_add_one] using congrArg Nat.pred (congrArg Nat.pred h)
    have h'' := congrArg (fun x : ℕ => x / 2) h'
    simpa [Nat.mul_comm] using h''
  have hsum_pair : Summable pair := by
    have hsum1 :
        Summable (fun m : ℕ => Real.log (2 * m + 2) / (((2 * m + 2 : ℕ) : ℝ) ^ s)) := by
      refine (hsum.comp_injective hodd_inj).congr ?_
      intro m
      dsimp [f]
      rw [show (((2 * m + 1 : ℕ) : ℝ) + 1) = 2 * (m : ℝ) + 2 by
        norm_num [Nat.cast_add, Nat.cast_mul, mul_comm]
        try ring]
      rw [show (((2 * m + 2 : ℕ) : ℝ)) = 2 * (m : ℝ) + 2 by
        norm_num [Nat.cast_add, Nat.cast_mul, mul_comm]
        try ring]
    have hsum2 :
        Summable (fun m : ℕ => Real.log (2 * m + 3) / (((2 * m + 3 : ℕ) : ℝ) ^ s)) := by
      refine (hsum.comp_injective hshift_inj).congr ?_
      intro m
      dsimp [f]
      rw [show (((2 * m + 2 : ℕ) : ℝ) + 1) = 2 * (m : ℝ) + 3 by
        norm_num [Nat.cast_add, Nat.cast_mul, mul_comm]
        try ring]
      rw [show (((2 * m + 3 : ℕ) : ℝ)) = 2 * (m : ℝ) + 3 by
        norm_num [Nat.cast_add, Nat.cast_mul, mul_comm]
        try ring]
    simpa [pair] using hsum1.sub hsum2
  have htail_nonneg : 0 ≤ ∑' m : ℕ, pair (m + 2) := by
    exact tsum_nonneg fun m => eta_deriv_pair_nonneg hs (by omega)
  have hsplit :
      ∑' m : ℕ, pair m = pair 0 + pair 1 + ∑' m : ℕ, pair (m + 2) := by
    calc
      ∑' m : ℕ, pair m = ∑ i ∈ Finset.range 2, pair i + ∑' m : ℕ, pair (m + 2) := by
        simpa using (hsum_pair.sum_add_tsum_nat_add 2).symm
      _ = pair 0 + pair 1 + ∑' m : ℕ, pair (m + 2) := by
          rw [Finset.sum_range_succ, Finset.sum_range_succ]
          simp [pair]
  have hfirst : 0 ≤ pair 0 + pair 1 := by
    dsimp [pair]
    norm_num
    nlinarith [first_eta_deriv_block_nonneg hs]
  rw [hderiv, hsplit]
  nlinarith

lemma etaSeries_pos {s : ℝ} (hs : 1 < s) :
    0 < etaSeries s := by
  have hfactor_pos : 0 < 1 - (2 : ℝ) ^ (1 - s) := by
    have hlt : (2 : ℝ) ^ (1 - s) < 1 := by
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    linarith
  have hzeta_bound : 1 / (s - 1) + (1 / 2 : ℝ) ≤ Erdos164.zetaSeries s := by
    simpa using Erdos164.zetaSeries_ge_one_div_sub_add_one_half hs
  have hzeta_pos : 0 < Erdos164.zetaSeries s := by
    have hs1 : 0 < s - 1 := by linarith
    have hlower : 0 < 1 / (s - 1) + (1 / 2 : ℝ) := by
      have : 0 < 1 / (s - 1 : ℝ) := one_div_pos.mpr hs1
      linarith
    exact lt_of_lt_of_le hlower hzeta_bound
  rw [etaSeries_eq_factor_mul_zetaSeries hs]
  exact mul_pos hfactor_pos hzeta_pos

lemma analyticSeries_eq_bound_sub_eta_log_deriv {s : ℝ} (hs : 1 < s) :
    Erdos164.analyticSeries s =
      Real.log (2 : ℝ) / ((2 : ℝ) ^ (s - 1) - 1) - deriv etaSeries s / etaSeries s := by
  have heta_event :
      etaSeries =ᶠ[nhds s] fun x : ℝ => (1 - (2 : ℝ) ^ (1 - x)) * Erdos164.zetaSeries x := by
    refine Filter.eventuallyEq_iff_exists_mem.mpr ?_
    refine ⟨{x : ℝ | 1 < x},
      (isOpen_lt continuous_const continuous_id).mem_nhds (by simpa using hs), ?_⟩
    intro x hx
    simpa using etaSeries_eq_factor_mul_zetaSeries hx
  have hfactor :
      HasDerivAt (fun x : ℝ => 1 - (2 : ℝ) ^ (1 - x))
        (Real.log (2 : ℝ) * (2 : ℝ) ^ (1 - s)) s := by
    have hpow :
        HasDerivAt (fun x : ℝ => (2 : ℝ) ^ (1 - x))
          (-(Real.log (2 : ℝ) * (2 : ℝ) ^ (1 - s))) s := by
      simpa [sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using
        ((hasDerivAt_const s 1).sub (hasDerivAt_id s)).const_rpow (by norm_num : 0 < (2 : ℝ))
    simpa using (hasDerivAt_const s 1).sub hpow
  have hprod :
      HasDerivAt
        (fun x : ℝ => (1 - (2 : ℝ) ^ (1 - x)) * Erdos164.zetaSeries x)
        (Real.log (2 : ℝ) * (2 : ℝ) ^ (1 - s) * Erdos164.zetaSeries s +
          (1 - (2 : ℝ) ^ (1 - s)) * deriv Erdos164.zetaSeries s) s := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hfactor.mul (zetaSeries_hasDerivAt hs)
  have hderiv_eta :
      deriv etaSeries s =
        Real.log (2 : ℝ) * (2 : ℝ) ^ (1 - s) * Erdos164.zetaSeries s +
          (1 - (2 : ℝ) ^ (1 - s)) * deriv Erdos164.zetaSeries s := by
    rw [Filter.EventuallyEq.deriv_eq heta_event]
    exact hprod.deriv
  have heta_val : etaSeries s = (1 - (2 : ℝ) ^ (1 - s)) * Erdos164.zetaSeries s := by
    simpa using etaSeries_eq_factor_mul_zetaSeries hs
  have hzeta_bound : 1 / (s - 1) + (1 / 2 : ℝ) ≤ Erdos164.zetaSeries s := by
    simpa using Erdos164.zetaSeries_ge_one_div_sub_add_one_half hs
  have hzeta_pos : 0 < Erdos164.zetaSeries s := by
    have hs1 : 0 < s - 1 := by linarith
    have hlower : 0 < 1 / (s - 1) + (1 / 2 : ℝ) := by
      have : 0 < 1 / (s - 1 : ℝ) := one_div_pos.mpr hs1
      linarith
    exact lt_of_lt_of_le hlower hzeta_bound
  have hfactor_pos : 0 < 1 - (2 : ℝ) ^ (1 - s) := by
    have hlt : (2 : ℝ) ^ (1 - s) < 1 := by
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    linarith
  have hzeta_ne : Erdos164.zetaSeries s ≠ 0 := hzeta_pos.ne'
  have hfactor_ne : 1 - (2 : ℝ) ^ (1 - s) ≠ 0 := hfactor_pos.ne'
  have hpow_ne : ((2 : ℝ) ^ (s - 1) - 1) ≠ 0 := by
    have hlt : 1 < (2 : ℝ) ^ (s - 1) := by
      exact Real.one_lt_rpow (by norm_num) (by linarith)
    linarith
  have hrew :
      Real.log (2 : ℝ) * (2 : ℝ) ^ (1 - s) / (1 - (2 : ℝ) ^ (1 - s)) =
        Real.log (2 : ℝ) / ((2 : ℝ) ^ (s - 1) - 1) := by
    have hpow_pos : 0 < (2 : ℝ) ^ (s - 1) := Real.rpow_pos_of_pos (by norm_num) (s - 1)
    have hneg : (2 : ℝ) ^ (1 - s) = ((2 : ℝ) ^ (s - 1))⁻¹ := by
      have : 1 - s = -(s - 1) := by ring
      rw [this, Real.rpow_neg (by norm_num : 0 ≤ (2 : ℝ))]
    rw [hneg]
    field_simp [hpow_ne, hpow_pos.ne']
  rw [Erdos164.analyticSeries_eq_neg_deriv_zetaSeries_div_zetaSeries hs, hderiv_eta, heta_val]
  calc
    -(deriv Erdos164.zetaSeries s) / Erdos164.zetaSeries s
        = Real.log (2 : ℝ) * (2 : ℝ) ^ (1 - s) / (1 - (2 : ℝ) ^ (1 - s)) -
            (Real.log (2 : ℝ) * (2 : ℝ) ^ (1 - s) * Erdos164.zetaSeries s +
              (1 - (2 : ℝ) ^ (1 - s)) * deriv Erdos164.zetaSeries s) /
            ((1 - (2 : ℝ) ^ (1 - s)) * Erdos164.zetaSeries s) := by
              field_simp [hzeta_ne, hfactor_ne]
              ring
    _ = Real.log (2 : ℝ) / ((2 : ℝ) ^ (s - 1) - 1) -
          (Real.log (2 : ℝ) * (2 : ℝ) ^ (1 - s) * Erdos164.zetaSeries s +
            (1 - (2 : ℝ) ^ (1 - s)) * deriv Erdos164.zetaSeries s) /
          ((1 - (2 : ℝ) ^ (1 - s)) * Erdos164.zetaSeries s) := by
            rw [hrew]

lemma analyticSeries_le_bound {t : ℝ} (ht : 0 < t) :
    Erdos164.analyticSeries (1 + t) ≤ Real.log (2 : ℝ) / ((2 : ℝ) ^ t - 1) := by
  have hs : 1 < 1 + t := by linarith
  have hmain := analyticSeries_eq_bound_sub_eta_log_deriv hs
  have hq :
      0 ≤ deriv etaSeries (1 + t) / etaSeries (1 + t) := by
    exact div_nonneg (etaSeries_deriv_nonneg hs) (etaSeries_pos hs).le
  have hpow : ((2 : ℝ) ^ ((1 + t) - 1) - 1) = ((2 : ℝ) ^ t - 1) := by ring_nf
  rw [hmain, hpow]
  linarith

theorem main_bound {n : ℕ} (hn : 1 < n) :
    series n ≤ 1 / Real.log ((2 * n : ℕ) : ℝ) := by
  let μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
  have h_nonneg :
      0 ≤ᵐ[μ] fun t : ℝ => kernel n t * Erdos164.analyticSeries (1 + t) := by
    filter_upwards [show ∀ᵐ t : ℝ ∂MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)),
        t ∈ Set.Ioi (0 : ℝ) from
          MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (kernel_nonneg (le_of_lt hn) ht) (analyticSeries_nonneg_shift t)
  have h_le :
      (fun t : ℝ => kernel n t * Erdos164.analyticSeries (1 + t)) ≤ᵐ[μ]
        (fun t : ℝ => (((2 * n : ℕ) : ℝ) ^ (-t))) := by
    filter_upwards [show ∀ᵐ t : ℝ ∂MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)),
        t ∈ Set.Ioi (0 : ℝ) from
          MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    calc
      kernel n t * Erdos164.analyticSeries (1 + t)
          ≤ kernel n t * (Real.log (2 : ℝ) / ((2 : ℝ) ^ t - 1)) := by
            exact mul_le_mul_of_nonneg_left (analyticSeries_le_bound ht)
              (kernel_nonneg (le_of_lt hn) ht)
      _ = (((2 * n : ℕ) : ℝ) ^ (-t)) := kernel_mul_bound_eq ht
  rw [series_eq_integral (le_of_lt hn)]
  have hmono :
      ∫ t, kernel n t * Erdos164.analyticSeries (1 + t) ∂μ ≤
        ∫ t, (((2 * n : ℕ) : ℝ) ^ (-t)) ∂μ := by
    exact MeasureTheory.integral_mono_of_nonneg h_nonneg (two_n_integrable hn) h_le
  calc
    ∫ t in Set.Ioi (0 : ℝ), kernel n t * Erdos164.analyticSeries (1 + t)
        = ∫ t, kernel n t * Erdos164.analyticSeries (1 + t) ∂μ := by
            rfl
    _ ≤ ∫ t, (((2 * n : ℕ) : ℝ) ^ (-t)) ∂μ := hmono
    _ = ∫ t in Set.Ioi (0 : ℝ), (((2 * n : ℕ) : ℝ) ^ (-t)) := by
          rfl
    _ = 1 / Real.log ((2 * n : ℕ) : ℝ) := integral_two_n_eq hn

#print axioms main_bound
-- 'Strong2.main_bound' depends on axioms: [propext, Classical.choice, Quot.sound]

end Strong2
