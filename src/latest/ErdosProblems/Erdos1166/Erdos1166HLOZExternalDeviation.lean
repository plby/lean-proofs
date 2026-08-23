import ErdosProblems.Erdos1166.Erdos1166HLOZFixedOriginKac

namespace Erdos1166.HLOZExternalDeviation

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal

open HLOZExternalUpper
open HLOZFixedOriginKac

/-!
The analytic end of HLOZ Lemma 2.5(2).  This file is deliberately stated
for an arbitrary bounded integer-valued local time.  The probabilistic input
is exactly the fixed-origin binomial-moment bound; no ordinary-SRW law is
substituted for the terminal-label external chain.
-/

/-- The optimizing Kac parameter, written without a negative real power. -/
noncomputable def kacParameter (n : ℕ) : ℝ :=
  let L := Real.log (n : ℝ)
  let P := L ^ rateExponent
  (L - P) / ((15 / (16 * Real.pi)) * L ^ 2)

noncomputable def logScale (n : ℕ) : ℝ := Real.log (n : ℝ)

noncomputable def rateScale (n : ℕ) : ℝ := logScale n ^ rateExponent

private theorem logScale_tendsto : Tendsto logScale atTop atTop := by
  exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

private theorem rateScale_tendsto : Tendsto rateScale atTop atTop := by
  exact (tendsto_rpow_atTop rateExponent_between_zero_and_one.1).comp
    logScale_tendsto

private lemma external_leading_pos : 0 < (15 / (16 * Real.pi) : ℝ) := by
  positivity

private lemma external_leading_inv_lt :
    ((15 / (16 * Real.pi) : ℝ))⁻¹ < 64 / 15 := by
  rw [inv_div]
  have hpi := Real.pi_lt_four
  apply (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 15)).2
  nlinarith

private lemma external_correction_lt :
    1 + 2 / (15 / (16 * Real.pi) : ℝ) < 193 / 25 := by
  have hpi := Real.pi_lt_d2
  have hpos := Real.pi_pos
  have heq : 2 / (15 / (16 * Real.pi) : ℝ) = 32 * Real.pi / 15 := by
    field_simp [ne_of_gt hpos]
    norm_num
  rw [heq]
  norm_num at hpi
  nlinarith

private theorem eventually_optimization_conditions (C : ℝ) (hC0 : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop,
      0 < logScale n ∧
      64 ≤ rateScale n ∧
      rateScale n ≤ logScale n ∧
      C ≤ (15 / (16 * Real.pi)) * rateScale n / 2 ∧
      4 * rateScale n ≤ (15 / (16 * Real.pi)) * logScale n ∧
      2 * logScale n / rateScale n ≤ Real.exp (rateScale n / 10) := by
  let p : ℝ := rateExponent
  let a : ℝ := 15 / (16 * Real.pi)
  have hp0 : 0 < p := rateExponent_between_zero_and_one.1
  have hp1 : p < 1 := rateExponent_between_zero_and_one.2
  have ha : 0 < a := external_leading_pos
  have hq : Tendsto (fun n : ℕ ↦ logScale n ^ (1 - p)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hp1)).comp logScale_tendsto
  have hexpRatio : Tendsto
      (fun n : ℕ ↦ Real.exp ((1 / 10 : ℝ) * rateScale n) /
        rateScale n ^ (1 : ℝ)) atTop atTop :=
    (tendsto_exp_mul_div_rpow_atTop 1 (1 / 10) (by norm_num)).comp
      rateScale_tendsto
  filter_upwards
      [logScale_tendsto.eventually_ge_atTop 1,
       rateScale_tendsto.eventually_ge_atTop 64,
       rateScale_tendsto.eventually_ge_atTop (2 * C / a),
       hq.eventually_ge_atTop (4 / a),
       hexpRatio.eventually_ge_atTop 2]
      with n hL1 hP64 hPC hq4 hexp2
  have hL0 : 0 < logScale n := lt_of_lt_of_le zero_lt_one hL1
  have hP0 : 0 < rateScale n := lt_of_lt_of_le (by norm_num) hP64
  have hPdef : rateScale n = logScale n ^ p := rfl
  have hPL : rateScale n ≤ logScale n := by
    rw [hPdef]
    exact Real.rpow_le_self_of_one_le hL1 hp1.le
  have hC : C ≤ a * rateScale n / 2 := by
    have hamul := mul_le_mul_of_nonneg_left hPC ha.le
    field_simp [ne_of_gt ha] at hamul ⊢
    linarith
  have hprod : rateScale n * logScale n ^ (1 - p) = logScale n := by
    rw [hPdef, ← Real.rpow_add hL0]
    convert Real.rpow_one (logScale n) using 2 <;> ring
  have hsep : 4 * rateScale n ≤ a * logScale n := by
    have hm := mul_le_mul_of_nonneg_left hq4 hP0.le
    rw [hprod] at hm
    have ham := mul_le_mul_of_nonneg_left hm ha.le
    field_simp [ne_of_gt ha] at ham
    nlinarith
  have hLPsq : logScale n ≤ rateScale n ^ 2 := by
    rw [hPdef, ← Real.rpow_mul_natCast hL0.le]
    apply Real.self_le_rpow_of_one_le hL1
    change 1 ≤ p * (2 : ℕ)
    norm_num [p, rateExponent_eq]
  have hLdiv : logScale n / rateScale n ≤ rateScale n :=
    (div_le_iff₀ hP0).2 (by simpa [pow_two] using hLPsq)
  have hexp2' : 2 * rateScale n ≤ Real.exp (rateScale n / 10) := by
    have := (mul_le_mul_of_nonneg_right hexp2 hP0.le)
    calc
      2 * rateScale n ≤
          (Real.exp ((1 / 10 : ℝ) * rateScale n) /
            rateScale n ^ (1 : ℝ)) * rateScale n := this
      _ = Real.exp (rateScale n / 10) := by
        rw [Real.rpow_one]
        field_simp [ne_of_gt hP0]
  have hratio : 2 * logScale n / rateScale n ≤
      Real.exp (rateScale n / 10) := by
    calc
      2 * logScale n / rateScale n = 2 * (logScale n / rateScale n) := by ring
      _ ≤ 2 * rateScale n := by gcongr
      _ ≤ Real.exp (rateScale n / 10) := hexp2'
  exact ⟨hL0, hP64, hPL, hC, hsep, hratio⟩

/-- A pointwise optimization lemma.  `L` is `log n`, `P=L^(16/25)`, and
`G` is the finite Green function.  The deliberately loose constants leave
room for the denominator of the geometric mgf. -/
private theorem optimized_mgf_pointwise
    {L P G C : ℝ}
    (hL : 0 < L) (hP : 64 ≤ P) (hPL : P ≤ L)
    (hC0 : 0 ≤ C)
    (hC : C ≤ (15 / (16 * Real.pi)) * P / 2)
    (hsep : 4 * P ≤ (15 / (16 * Real.pi)) * L)
    (hratio : 2 * L / P ≤ Real.exp (P / 10))
    (hG0 : 0 ≤ G)
    (hG : G ≤ (15 / (16 * Real.pi)) * L + C) :
    let a : ℝ := 15 / (16 * Real.pi)
    let T : ℝ := a * L ^ 2 - 2 * L * P
    let u : ℝ := (L - P) / (a * L ^ 2)
    0 ≤ u ∧ u * G < 1 ∧ 0 ≤ T ∧
      1 / ((1 + u) ^ ⌈T⌉₊ * (1 - u * G)) ≤
        Real.exp (8 * P - L) := by
  dsimp
  let a : ℝ := 15 / (16 * Real.pi)
  let T : ℝ := a * L ^ 2 - 2 * L * P
  let u : ℝ := (L - P) / (a * L ^ 2)
  let d : ℝ := P / (2 * L)
  have ha : 0 < a := by exact external_leading_pos
  have hL2 : 0 < L ^ 2 := sq_pos_of_pos hL
  have hden : 0 < a * L ^ 2 := mul_pos ha hL2
  have hu0 : 0 ≤ u := div_nonneg (sub_nonneg.mpr hPL) hden.le
  have hP0 : 0 < P := lt_of_lt_of_le (by norm_num) hP
  have hd0 : 0 < d := div_pos hP0 (by positivity)
  have hdle : d ≤ 1 / 2 := by
    dsimp [d]
    exact (div_le_iff₀ (by positivity : 0 < 2 * L)).2 (by nlinarith)
  have hT0 : 0 ≤ T := by
    dsimp [T]
    nlinarith [mul_nonneg hL.le (show 0 ≤ a * L - 2 * P by nlinarith)]
  have huG : u * G ≤ 1 - d := by
    calc
      u * G ≤ u * (a * L + C) := mul_le_mul_of_nonneg_left hG hu0
      _ ≤ 1 - d := by
        dsimp [u, d]
        have hCL : C ≤ a * P / 2 := hC
        have hcross : 0 ≤ P * C := mul_nonneg hP0.le hC0
        field_simp [ne_of_gt ha, ne_of_gt hL]
        nlinarith
  have huGlt : u * G < 1 := lt_of_le_of_lt huG (by linarith)
  refine ⟨hu0, huGlt, hT0, ?_⟩
  have hlog : u - u ^ 2 ≤ Real.log (1 + u) := by
    have hlo := Real.le_log_one_add_of_nonneg hu0
    apply (show u - u ^ 2 ≤ 2 * u / (u + 2) by
      have hden2 : 0 < u + 2 := by linarith
      rw [le_div_iff₀ hden2]
      nlinarith [sq_nonneg u]).trans hlo
  have hu_le : u ≤ 1 / (a * L) := by
    dsimp [u]
    rw [div_le_iff₀ hden, div_eq_mul_inv]
    field_simp [ne_of_gt ha, ne_of_gt hL]
    nlinarith
  have hTu : L - (193 / 25) * P ≤ T * u := by
    have hc := external_correction_lt
    change 1 + 2 / a < 193 / 25 at hc
    have hcoef : (1 + 2 / a) * P ≤ (193 / 25) * P :=
      mul_le_mul_of_nonneg_right hc.le hP0.le
    have hnonneg : 0 ≤ 2 / a * P ^ 2 / L := by positivity
    dsimp [T, u]
    have hident :
        (a * L ^ 2 - 2 * L * P) * ((L - P) / (a * L ^ 2)) =
          L - (1 + 2 / a) * P + (2 / a) * P ^ 2 / L := by
      field_simp [ne_of_gt ha, ne_of_gt hL]
      ring
    rw [hident]
    linarith
  have hTu2 : T * u ^ 2 ≤ (2 / 25) * P := by
    have hTupper : T ≤ a * L ^ 2 := by
      dsimp [T]
      nlinarith [mul_nonneg hL.le hP0.le]
    have huSq : u ^ 2 ≤ (1 / (a * L)) ^ 2 := by
      exact (sq_le_sq₀ hu0 (by positivity)).2 hu_le
    have hnonnegT : 0 ≤ T := hT0
    calc
      T * u ^ 2 ≤ (a * L ^ 2) * (1 / (a * L)) ^ 2 := by
        exact mul_le_mul hTupper huSq (sq_nonneg _) (mul_nonneg ha.le (sq_nonneg L))
      _ = a⁻¹ := by field_simp [ne_of_gt ha, ne_of_gt hL]
      _ ≤ (2 / 25) * P := by
        have hinv := external_leading_inv_lt
        nlinarith
  have hTexponent : L - (39 / 5) * P ≤ T * (u - u ^ 2) := by
    rw [mul_sub]
    nlinarith [hTu, hTu2]
  have hceil : T ≤ (⌈T⌉₊ : ℝ) := Nat.le_ceil T
  have hlog0 : 0 ≤ Real.log (1 + u) := Real.log_nonneg (by linarith)
  have hpowLower :
      Real.exp (L - (39 / 5) * P) ≤ (1 + u) ^ ⌈T⌉₊ := by
    rw [← Real.exp_log (by linarith : 0 < 1 + u), ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    calc
      L - (39 / 5) * P ≤ T * (u - u ^ 2) := hTexponent
      _ ≤ T * Real.log (1 + u) := mul_le_mul_of_nonneg_left hlog hT0
      _ ≤ (⌈T⌉₊ : ℝ) * Real.log (1 + u) :=
        mul_le_mul_of_nonneg_right hceil hlog0
  have hdenFloor : d ≤ 1 - u * G := by linarith
  have hprodPos : 0 < (1 + u) ^ ⌈T⌉₊ * (1 - u * G) := by
    exact mul_pos (pow_pos (by linarith) _) (sub_pos.mpr huGlt)
  have hrough :
      1 / ((1 + u) ^ ⌈T⌉₊ * (1 - u * G)) ≤
        1 / (Real.exp (L - (39 / 5) * P) * d) := by
    apply one_div_le_one_div_of_le
    · exact mul_pos (Real.exp_pos _) hd0
    · exact mul_le_mul hpowLower hdenFloor hd0.le (pow_nonneg (by linarith) _)
  calc
    1 / ((1 + u) ^ ⌈T⌉₊ * (1 - u * G)) ≤
        1 / (Real.exp (L - (39 / 5) * P) * d) := hrough
    _ = Real.exp (-(L - (39 / 5) * P)) * (2 * L / P) := by
      rw [one_div, mul_inv_rev, ← Real.exp_neg]
      dsimp [d]
      field_simp [ne_of_gt hP0, ne_of_gt hL]
    _ ≤ Real.exp (-(L - (39 / 5) * P)) * Real.exp (P / 10) := by
      gcongr
    _ = Real.exp ((79 / 10) * P - L) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (8 * P - L) := by
      apply Real.exp_le_exp.mpr
      linarith

private theorem externalThreshold_eq_scales {n : ℕ} (hL : 0 < logScale n) :
    externalThreshold n =
      (15 / (16 * Real.pi)) * logScale n ^ 2 -
        2 * logScale n * rateScale n := by
  have hb : HLOZExternalUpper.beta = rateExponent + 1 := by
    linarith [beta_sub_one_eq_rateExponent]
  rw [externalThreshold, hb]
  change
    15 / (16 * Real.pi) * logScale n ^ 2 -
        2 * logScale n ^ (rateExponent + 1) = _
  rw [Real.rpow_add hL, Real.rpow_one]
  simp only [rateScale]
  ring

private theorem externalRate_eq_scales {n : ℕ} (hn : 0 < n) :
    externalRate n = Real.exp (8 * rateScale n - logScale n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [externalRate]
  change Real.exp (8 * rateScale n) / (n : ℝ) = _
  rw [← Real.exp_log hnR, ← Real.exp_sub]
  rfl

/-- The complete analytic conversion used by HLOZ (2.19).  The sole
probabilistic premise is the fixed-origin binomial Kac bound with a Green
function having the sharp external-chain leading coefficient. -/
theorem eventually_externalThreshold_measureReal_le_rate_of_binomial_moments
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (localTimeFn : ℕ → Ω → ℕ)
    (hlocalMeas : ∀ n, Measurable (localTimeFn n))
    (hlocalBound : ∀ n ω, localTimeFn n ω ≤ n + 1)
    (G : ℕ → ℝ) (hG0 : ∀ n, 0 ≤ G n)
    (hGreen : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      G n ≤ 15 / (16 * Real.pi) * Real.log (n : ℝ) + C)
    (hmoment : ∀ n r, r ≤ n + 1 →
      ∫ ω, ((localTimeFn n ω).choose r : ℝ) ∂μ ≤ G n ^ r) :
    ∀ᶠ n : ℕ in atTop,
      μ.real {ω | externalThreshold n ≤ (localTimeFn n ω : ℝ)} ≤
        externalRate n := by
  obtain ⟨C, hGreen⟩ := hGreen
  let C' : ℝ := max C 0
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hGreen' : ∀ᶠ n : ℕ in atTop,
      G n ≤ 15 / (16 * Real.pi) * logScale n + C' := by
    filter_upwards [hGreen] with n hn
    dsimp [logScale, C']
    linarith [le_max_left C 0]
  filter_upwards [eventually_optimization_conditions C' hC'0, hGreen',
      eventually_gt_atTop 0]
      with n hnopt hGn hnpos
  rcases hnopt with ⟨hL, hP64, hPL, hC, hsep, hratio⟩
  let T : ℝ := (15 / (16 * Real.pi)) * logScale n ^ 2 -
    2 * logScale n * rateScale n
  let u : ℝ := (logScale n - rateScale n) /
    ((15 / (16 * Real.pi)) * logScale n ^ 2)
  have hopt := optimized_mgf_pointwise hL hP64 hPL hC'0 hC hsep hratio
    (hG0 n) hGn
  change 0 ≤ u ∧ u * G n < 1 ∧ 0 ≤ T ∧
      1 / ((1 + u) ^ ⌈T⌉₊ * (1 - u * G n)) ≤
        Real.exp (8 * rateScale n - logScale n) at hopt
  rcases hopt with ⟨hu0, huG, hT0, hoptimized⟩
  have htail := measureReal_ge_le_of_binomial_moments
    μ (localTimeFn n) (hlocalMeas n) (n + 1) (hlocalBound n)
    (G n) u (hG0 n) hu0 huG (hmoment n) ⌈T⌉₊
  have hthreshold : externalThreshold n = T := by
    exact externalThreshold_eq_scales hL
  have hevent :
      {ω | externalThreshold n ≤ (localTimeFn n ω : ℝ)} =
        {ω | ⌈T⌉₊ ≤ localTimeFn n ω} := by
    ext ω
    rw [hthreshold]
    exact (Nat.ceil_le (a := T) (n := localTimeFn n ω)).symm
  rw [hevent]
  exact htail.trans (hoptimized.trans_eq
    (externalRate_eq_scales hnpos).symm)

/-- Fixed-origin Kac plus the analytic optimization, packaged in the form
needed by the terminal-label chain.  A caller has to prove only the exact
successive-gap return-kernel inequality and the sharp Green bound. -/
theorem eventually_externalThreshold_measureReal_le_rate_of_fixedOriginKac
    {Site' Ω : Type*} [DecidableEq Site'] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ∀ n : ℕ, Ω → Fin (n + 1) → Site') (x : Site')
    (hlocalMeas : ∀ n, Measurable
      (fun ω ↦ KacMoment.finiteLocalTime n (X n ω) x))
    (hHitMeas : ∀ n r (t : KacMoment.TimeTuple n r),
      MeasurableSet (fixedHitSet n r (X n) x t))
    (q : ∀ n : ℕ, Fin (n + 1) → ℝ)
    (hq : ∀ n d, 0 ≤ q n d)
    (hKernel : ∀ n k
      (t : KacMoment.TimeTuple n (k + 1)),
      t ∈ KacMoment.sortedTuples n (k + 1) →
      μ.real (fixedHitSet n (k + 1) (X n) x t) ≤
        fixedGapWeight n k (q n) t)
    (hGreen : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      (∑ d : Fin (n + 1), q n d) ≤
        15 / (16 * Real.pi) * Real.log (n : ℝ) + C) :
    ∀ᶠ n : ℕ in atTop,
      μ.real {ω | externalThreshold n ≤
        (KacMoment.finiteLocalTime n (X n ω) x : ℝ)} ≤
          externalRate n := by
  let localTimeFn : ℕ → Ω → ℕ :=
    fun n ω ↦ KacMoment.finiteLocalTime n (X n ω) x
  let G : ℕ → ℝ := fun n ↦ ∑ d : Fin (n + 1), q n d
  have hbound : ∀ n ω, localTimeFn n ω ≤ n + 1 := by
    intro n ω
    dsimp [localTimeFn, KacMoment.finiteLocalTime]
    simpa using Finset.card_le_card
      (Finset.filter_subset (fun i : Fin (n + 1) ↦ X n ω i = x)
        Finset.univ)
  have hG0 : ∀ n, 0 ≤ G n := by
    intro n
    exact Finset.sum_nonneg fun d _ ↦ hq n d
  have hmoments : ∀ n r, r ≤ n + 1 →
      ∫ ω, ((localTimeFn n ω).choose r : ℝ) ∂μ ≤ G n ^ r := by
    intro n r _hr
    cases r with
    | zero =>
        simp [localTimeFn, G]
    | succ k =>
        exact integral_choose_finiteLocalTime_le_green_pow
          n k (X n) x μ (hHitMeas n (k + 1)) (q n) (hq n)
          (hKernel n k)
  exact eventually_externalThreshold_measureReal_le_rate_of_binomial_moments
    μ localTimeFn (by exact hlocalMeas) hbound G hG0 hGreen hmoments

end Erdos1166.HLOZExternalDeviation
