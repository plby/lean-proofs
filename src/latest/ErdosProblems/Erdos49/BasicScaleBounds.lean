import ErdosProblems.Erdos49.ClusterScaleBounds

/-!
# The four elementary exceptional sets at Tao's scales

We now estimate the small, smooth, repeated-factor, and large-smooth-part
pieces.  The Rankin exponent is expanded explicitly; no asymptotic notation
is used in these statements.
-/

open Filter Set Topology

namespace Erdos49

noncomputable section

lemma scale_logD_lower {N : ℕ} (hs : ScaleFacts N) :
    scaleT N ^ 4 ≤ Real.log (scaleD N : ℝ) := by
  calc
    scaleT N ^ 4 = Real.log (Real.exp (scaleT N ^ 4)) := by
      rw [Real.log_exp]
    _ ≤ Real.log (scaleD N : ℝ) :=
      Real.log_le_log (Real.exp_pos _) hs.D_bounds.1

lemma scale_inv_L_le_error_ratio {N : ℕ} (hs : ScaleFacts N) :
    (1 : ℝ) / scaleL N ≤
      scaleT N ^ 5 / Real.log (N : ℝ) ^ 2 := by
  let t := scaleT N
  let h := Real.log (N : ℝ)
  have ht : 0 < t := by dsimp only [t]; linarith [hs.t_ge]
  have hh : 0 < h := by dsimp only [h]; linarith [scale_h_ge hs]
  have hL : Real.exp (20 * t) ≤ (scaleL N : ℝ) := by
    simpa [t] using hs.L_bounds.1
  have hinv : (1 : ℝ) / scaleL N ≤ Real.exp (-20 * t) := by
    calc
      (1 : ℝ) / scaleL N ≤ 1 / Real.exp (20 * t) := by
        exact one_div_le_one_div_of_le (Real.exp_pos _) hL
      _ = Real.exp (-20 * t) := by
        rw [show -20 * t = -(20 * t) by ring, Real.exp_neg]
        rw [one_div]
  have hpow : (1 : ℝ) ≤ t ^ 5 := by
    have ht10 : (10 : ℝ) ≤ t := by simpa [t] using hs.t_ge
    have ht1 : (1 : ℝ) ≤ t := by linarith
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) ht1 5
  calc
    (1 : ℝ) / scaleL N ≤ Real.exp (-20 * t) := hinv
    _ ≤ Real.exp (-2 * t) := Real.exp_le_exp.mpr (by nlinarith)
    _ ≤ t ^ 5 * Real.exp (-2 * t) := by
      nlinarith [Real.exp_pos (-2 * t)]
    _ = t ^ 5 / h ^ 2 := by
      have hexp : Real.exp (-2 * t) = 1 / (Real.exp t) ^ 2 := by
        rw [show -2 * t = -(t + t) by ring, Real.exp_neg, Real.exp_add]
        ring
      rw [hexp, show Real.exp t = h by simpa [t, h] using scale_exp_t hs]
      ring
    _ = scaleT N ^ 5 / Real.log (N : ℝ) ^ 2 := by rfl

lemma smallExceptional_le_errorScale {N : ℕ} (hs : ScaleFacts N) :
    ((smallExceptional N (scaleL N)).card : ℝ) ≤ taoErrorScale N := by
  have hsmall := smallExceptional_card_le (N := N) hs.L_pos
  calc
    ((smallExceptional N (scaleL N)).card : ℝ) ≤
        ((N / scaleL N : ℕ) : ℝ) := by exact_mod_cast hsmall
    _ ≤ (N : ℝ) / scaleL N := Nat.cast_div_le
    _ = (N : ℝ) * ((1 : ℝ) / scaleL N) := by ring
    _ ≤ (N : ℝ) *
        (scaleT N ^ 5 / Real.log (N : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_left (scale_inv_L_le_error_ratio hs)
        (Nat.cast_nonneg N)
    _ = taoErrorScale N := by unfold taoErrorScale; ring

lemma squareExceptional_le_errorScale {N : ℕ} (hs : ScaleFacts N) :
    ((squareExceptional N (scaleL N)).card : ℝ) ≤ taoErrorScale N := by
  calc
    ((squareExceptional N (scaleL N)).card : ℝ) ≤
        (N : ℝ) / scaleL N := squareExceptional_card_real_le hs.L_pos
    _ = (N : ℝ) * ((1 : ℝ) / scaleL N) := by ring
    _ ≤ (N : ℝ) *
        (scaleT N ^ 5 / Real.log (N : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_left (scale_inv_L_le_error_ratio hs)
        (Nat.cast_nonneg N)
    _ = taoErrorScale N := by unfold taoErrorScale; ring

lemma scale_D_rankin_power_upper {N : ℕ} (hs : ScaleFacts N) :
    (scaleD N : ℝ) ^ (rankinAlpha (scaleL N) - 1) ≤
      Real.exp (-(scaleT N ^ 3 / 42)) := by
  let t := scaleT N
  let logL := Real.log (scaleL N : ℝ)
  let logD := Real.log (scaleD N : ℝ)
  have ht : 0 < t := by dsimp only [t]; linarith [hs.t_ge]
  have hLexp := scale_L_gt_exp_one hs
  have hlogL : 1 < logL := by
    dsimp only [logL]
    rw [Real.lt_log_iff_exp_lt (by exact_mod_cast hs.L_pos)]
    exact hLexp
  have hlogLup : logL ≤ 21 * t := by
    simpa [logL, t] using scale_logL_upper hs
  have hlogDlow : t ^ 4 ≤ logD := by
    simpa [logD, t] using scale_logD_lower hs
  have hfrac : t ^ 3 / 42 ≤ logD / (2 * logL) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * logL)).2
    calc
      (t ^ 3 / 42) * (2 * logL) ≤
          (t ^ 3 / 42) * (42 * t) := by
        apply mul_le_mul_of_nonneg_left
        · nlinarith [hlogLup]
        · positivity
      _ = t ^ 4 := by field_simp
      _ ≤ logD := hlogDlow
  have hDpos : (0 : ℝ) < scaleD N := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hs.D_one)
  rw [Real.rpow_def_of_pos hDpos]
  apply Real.exp_le_exp.mpr
  unfold rankinAlpha
  dsimp only [logL, logD, t] at hfrac ⊢
  have hlogL0 : Real.log (scaleL N : ℝ) ≠ 0 := by
    linarith
  calc
    Real.log (scaleD N : ℝ) *
        (1 - 1 / (2 * Real.log (scaleL N : ℝ)) - 1) =
        -(Real.log (scaleD N : ℝ) /
          (2 * Real.log (scaleL N : ℝ))) := by field_simp; ring
    _ ≤ -(scaleT N ^ 3 / 42) := neg_le_neg hfrac

lemma scale_R_rankin_power_upper {N : ℕ} (hs : ScaleFacts N) :
    (N : ℝ) ^ rankinAlpha (scaleR N) ≤
      (N : ℝ) * Real.exp (-250 * scaleT N) := by
  let t := scaleT N
  let h := Real.log (N : ℝ)
  let logR := Real.log (scaleR N : ℝ)
  have ht : 0 < t := by dsimp only [t]; linarith [hs.t_ge]
  have hh : 0 < h := by dsimp only [h]; linarith [scale_h_ge hs]
  have hRexp : Real.exp 1 < (scaleR N : ℝ) := by
    have hLR := hs.separation.1
    exact (scale_L_gt_exp_one hs).trans_le (by exact_mod_cast hLR.le)
  have hlogR : 1 < logR := by
    dsimp only [logR]
    rw [Real.lt_log_iff_exp_lt ((Real.exp_pos 1).trans hRexp)]
    exact hRexp
  have hlogRup : logR ≤ h / (500 * t) := by
    simpa [logR, h, t] using hs.logR_upper
  have hfrac : 250 * t ≤ h / (2 * logR) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * logR)).2
    calc
      (250 * t) * (2 * logR) ≤
          (250 * t) * (2 * (h / (500 * t))) := by gcongr
      _ = h := by field_simp; ring
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hs.N_pos
  rw [Real.rpow_def_of_pos hNpos]
  unfold rankinAlpha
  have hlogR0 : logR ≠ 0 := by linarith
  have hexponent : Real.log (N : ℝ) *
      (1 - 1 / (2 * Real.log (scaleR N : ℝ))) =
      Real.log (N : ℝ) + -(h / (2 * logR)) := by
    dsimp only [h, logR]
    field_simp
    ring
  calc
    Real.exp (Real.log (N : ℝ) *
        (1 - 1 / (2 * Real.log (scaleR N : ℝ)))) =
        (N : ℝ) * Real.exp (-(h / (2 * logR))) := by
      rw [hexponent, Real.exp_add, Real.exp_log hNpos]
    _ ≤ (N : ℝ) * Real.exp (-250 * t) := by
      gcongr
      simpa only [neg_mul] using neg_le_neg hfrac
    _ = (N : ℝ) * Real.exp (-250 * scaleT N) := by rfl

lemma exp_neg_250_mul_h_pow_le_error_ratio {N : ℕ} (hs : ScaleFacts N) :
    Real.exp (-250 * scaleT N) * Real.log (N : ℝ) ^ 8 ≤
      scaleT N ^ 5 / Real.log (N : ℝ) ^ 2 := by
  let t := scaleT N
  let h := Real.log (N : ℝ)
  have ht : 0 < t := by dsimp only [t]; linarith [hs.t_ge]
  have hh : 0 < h := by dsimp only [h]; linarith [scale_h_ge hs]
  apply (le_div_iff₀ (sq_pos_of_pos hh)).2
  have ht5 : (1 : ℝ) ≤ t ^ 5 := by
    have ht10 : (10 : ℝ) ≤ t := by simpa [t] using hs.t_ge
    have ht1 : (1 : ℝ) ≤ t := by linarith
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) ht1 5
  change Real.exp (-250 * t) * h ^ 8 * h ^ 2 ≤ t ^ 5
  rw [show h = Real.exp t by simpa [h, t] using (scale_exp_t hs).symm]
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
  rw [← Real.exp_add, ← Real.exp_add]
  norm_num only [Nat.cast_ofNat]
  exact (Real.exp_le_one_iff.mpr (by nlinarith)).trans ht5

lemma rankinEulerProduct_nonneg {y : ℕ} (hy : Real.exp 1 < (y : ℝ)) :
    0 ≤ rankinEulerProduct y := by
  unfold rankinEulerProduct
  apply Finset.prod_nonneg
  intro p hp
  apply inv_nonneg.mpr
  exact sub_nonneg.mpr (rankin_prime_ratio_lt_one hy
    (Nat.prime_of_mem_primesLE hp)).le

theorem eventually_basicExceptional_bounds :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      ((smallExceptional N (scaleL N)).card : ℝ) +
        (smoothExceptional N (scaleR N)).card +
        (squareExceptional N (scaleL N)).card +
        (smoothTailExceptional N (scaleL N) (scaleD N)).card ≤
          C * taoErrorScale N := by
  obtain ⟨Cr, hCr, hprod⟩ := exists_rankinEulerProduct_log_bound
  let Ctail := Cr * (21 : ℝ) ^ 8
  let C := 3 + Cr
  refine ⟨C, by dsimp only [C, Ctail]; positivity, ?_⟩
  have hdecay := eventually_cubic_tail_decay Ctail (by
    dsimp only [Ctail]
    positivity)
  filter_upwards [eventually_scaleFacts, scale_log_tendsto.eventually hdecay]
    with N hs htailDecay
  have hLexp := scale_L_gt_exp_one hs
  have hRexp : Real.exp 1 < (scaleR N : ℝ) := by
    exact hLexp.trans_le (by exact_mod_cast hs.separation.1.le)
  have hprodL := hprod (scaleL N) hLexp
  have hprodR := hprod (scaleR N) hRexp
  have hlogL0 : 0 ≤ Real.log (scaleL N : ℝ) := by
    have : (1 : ℝ) ≤ scaleL N := by exact_mod_cast (show 1 ≤ scaleL N from hs.L_pos)
    exact Real.log_nonneg this
  have ht0 : 0 ≤ scaleT N := by linarith [hs.t_ge]
  have hprodL' : rankinEulerProduct (scaleL N) ≤
      Ctail * scaleT N ^ 8 := by
    calc
      rankinEulerProduct (scaleL N) ≤
          Cr * Real.log (scaleL N : ℝ) ^ 8 := hprodL
      _ ≤ Cr * (21 * scaleT N) ^ 8 := by
        gcongr
        exact scale_logL_upper hs
      _ = Ctail * scaleT N ^ 8 := by
        dsimp only [Ctail]
        ring
  have hlogRpos : 0 ≤ Real.log (scaleR N : ℝ) := by
    exact Real.log_nonneg
      ((Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hRexp.le)
  have hlogRh : Real.log (scaleR N : ℝ) ≤ Real.log (N : ℝ) := by
    have hh := scale_h_ge hs
    have ht := hs.t_ge
    calc
      Real.log (scaleR N : ℝ) ≤
          Real.log (N : ℝ) / (500 * scaleT N) := hs.logR_upper
      _ ≤ Real.log (N : ℝ) := by
        apply div_le_self
        · linarith
        · nlinarith
  have hprodR' : rankinEulerProduct (scaleR N) ≤
      Cr * Real.log (N : ℝ) ^ 8 := by
    exact hprodR.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hlogRpos hlogRh 8) hCr)
  have hprodL0 : 0 ≤ rankinEulerProduct (scaleL N) :=
    rankinEulerProduct_nonneg hLexp
  have hprodR0 : 0 ≤ rankinEulerProduct (scaleR N) :=
    rankinEulerProduct_nonneg hRexp
  have hsmooth := smoothExceptional_card_real_le hs.N_pos hRexp
  have hsmooth' : ((smoothExceptional N (scaleR N)).card : ℝ) ≤
      Cr * taoErrorScale N := by
    calc
      ((smoothExceptional N (scaleR N)).card : ℝ) ≤
          (N : ℝ) ^ rankinAlpha (scaleR N) *
            rankinEulerProduct (scaleR N) := hsmooth
      _ ≤ ((N : ℝ) * Real.exp (-250 * scaleT N)) *
          (Cr * Real.log (N : ℝ) ^ 8) := by
        exact mul_le_mul (scale_R_rankin_power_upper hs) hprodR'
          hprodR0 (by positivity)
      _ ≤ Cr * taoErrorScale N := by
        have hr := exp_neg_250_mul_h_pow_le_error_ratio hs
        calc
          ((N : ℝ) * Real.exp (-250 * scaleT N)) *
              (Cr * Real.log (N : ℝ) ^ 8) =
              (Cr * (N : ℝ)) *
                (Real.exp (-250 * scaleT N) *
                  Real.log (N : ℝ) ^ 8) := by ring
          _ ≤ (Cr * (N : ℝ)) *
              (scaleT N ^ 5 / Real.log (N : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hr (mul_nonneg hCr (Nat.cast_nonneg N))
          _ = Cr * taoErrorScale N := by unfold taoErrorScale; ring
  have hsmoothTail := smoothTailExceptional_card_real_le
    (N := N) (L := scaleL N) (D := scaleD N)
    (lt_of_lt_of_le Nat.zero_lt_one hs.D_one) hLexp
  have hsmoothTail' :
      ((smoothTailExceptional N (scaleL N) (scaleD N)).card : ℝ) ≤
        taoErrorScale N := by
    have hpow := scale_D_rankin_power_upper hs
    calc
      ((smoothTailExceptional N (scaleL N) (scaleD N)).card : ℝ) ≤
          (N : ℝ) * ((scaleD N : ℝ) ^
            (rankinAlpha (scaleL N) - 1) *
              rankinEulerProduct (scaleL N)) := hsmoothTail
      _ ≤ (N : ℝ) * (Real.exp (-(scaleT N ^ 3 / 42)) *
          (Ctail * scaleT N ^ 8)) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul hpow hprodL' hprodL0 (by positivity)
        · exact Nat.cast_nonneg N
      _ ≤ taoErrorScale N := by
        have hexp : Real.exp (-(scaleT N ^ 3 / 42)) =
            Real.exp (-2 * scaleT N) *
              Real.exp (2 * scaleT N - scaleT N ^ 3 / 42) := by
          rw [← Real.exp_add]
          congr 1 <;> ring
        rw [hexp]
        have hh := scale_exp_t hs
        unfold taoErrorScale
        rw [← hh]
        have hexp2 : Real.exp (-2 * scaleT N) =
            1 / Real.exp (scaleT N) ^ 2 := by
          rw [show -2 * scaleT N =
            -(scaleT N + scaleT N) by ring, Real.exp_neg, Real.exp_add]
          ring
        rw [show (N : ℝ) *
              (Real.exp (-2 * scaleT N) *
                Real.exp (2 * scaleT N - scaleT N ^ 3 / 42) *
                  (Ctail * scaleT N ^ 8)) =
            ((N : ℝ) * scaleT N ^ 5 /
              Real.exp (scaleT N) ^ 2) *
              (Ctail * scaleT N ^ 3 *
                Real.exp (2 * scaleT N - scaleT N ^ 3 / 42)) by
          rw [hexp2]
          ring]
        have hP : 0 ≤ (N : ℝ) * scaleT N ^ 5 /
            Real.exp (scaleT N) ^ 2 := by positivity
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left htailDecay hP
  have hsmall := smallExceptional_le_errorScale hs
  have hsquare := squareExceptional_le_errorScale hs
  calc
    ((smallExceptional N (scaleL N)).card : ℝ) +
        (smoothExceptional N (scaleR N)).card +
        (squareExceptional N (scaleL N)).card +
        (smoothTailExceptional N (scaleL N) (scaleD N)).card ≤
      taoErrorScale N + Cr * taoErrorScale N + taoErrorScale N +
        taoErrorScale N := by linarith
    _ = C * taoErrorScale N := by dsimp only [C]; ring

#print axioms eventually_basicExceptional_bounds

end

end Erdos49
