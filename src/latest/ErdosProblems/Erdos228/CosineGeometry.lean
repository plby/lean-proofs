import ErdosProblems.Erdos228.CosineDerivatives

namespace Erdos228.CosineConstruction

open Set

noncomputable section

/-- Distinct maximal bad runs are linearly ordered and disjoint. -/
private theorem maximalBadRuns_oriented {N a b c d : ℕ} {bad : ℕ → Prop}
    [DecidablePred bad]
    (h₁ : Erdos228.Intervals.IsMaximalBadRun N bad a b)
    (h₂ : Erdos228.Intervals.IsMaximalBadRun N bad c d)
    (hne : (a, b) ≠ (c, d)) :
    b < c ∨ d < a := by
  rcases lt_trichotomy a c with hac | hac | hca
  · left
    by_contra hbc
    have hcb : c ≤ b := Nat.le_of_not_gt hbc
    have hcpos : 0 < c := by omega
    have hcPredN : c - 1 < N :=
      lt_of_le_of_lt (Nat.sub_le c 1) (hcb.trans_lt h₁.2.1)
    have hbadPred : bad (c - 1) :=
      h₁.2.2.1 (c - 1) (Finset.mem_range.mpr hcPredN) (by omega) (by omega)
    rcases h₂.2.2.2.1 with hc0 | hgoodPred
    · omega
    · exact hgoodPred hbadPred
  · exact False.elim (hne (h₁.eq_of_start_eq h₂ hac))
  · right
    by_contra hda
    have had : a ≤ d := Nat.le_of_not_gt hda
    have hapos : 0 < a := by omega
    have haPredN : a - 1 < N :=
      lt_of_le_of_lt (Nat.sub_le a 1) (had.trans_lt h₂.2.1)
    have hbadPred : bad (a - 1) :=
      h₂.2.2.1 (a - 1) (Finset.mem_range.mpr haPredN) (by omega) (by omega)
    rcases h₁.2.2.2.1 with ha0 | hgoodPred
    · omega
    · exact hgoodPred hbadPred

/-- The closed grid intervals attached to distinct first-quadrant dangerous
runs are separated by at least one grid spacing.  Equality can occur at the
two facing grid endpoints when exactly one good cell lies between the runs. -/
theorem firstQuadrantIntervals_pairwise_separated
    {n t : ℕ} {gamma : ℝ} (hn : 0 < n) :
    Set.Pairwise
      (↑(firstQuadrantIntervals n t gamma) :
        Set Erdos228.OddSine.RealInterval)
      (fun I J ↦ ∀ x ∈ Icc I.1 I.2, ∀ y ∈ Icc J.1 J.2,
        Real.pi / n ≤ |x - y|) := by
  classical
  intro I hI J hJ hne x hx y hy
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hI
  obtain ⟨⟨c, d⟩, hcd, rfl⟩ := Finset.mem_image.mp hJ
  have hrunsNe : (a, b) ≠ (c, d) := by
    intro heq
    apply hne
    exact congrArg (runEndpoints n) heq
  rw [mem_firstQuadrantRuns] at hab hcd
  have horient := maximalBadRuns_oriented
    (show Erdos228.Intervals.IsMaximalBadRun (2 * n) (BadCell n t gamma) a b by
      simpa only [mem_dangerousRuns] using hab.1)
    (show Erdos228.Intervals.IsMaximalBadRun (2 * n) (BadCell n t gamma) c d by
      simpa only [mem_dangerousRuns] using hcd.1)
    hrunsNe
  simp only [runEndpoints, mem_Icc] at hx hy ⊢
  have hmono := Erdos228.Intervals.gridPoint_mono hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmesh : 0 < Real.pi / (n : ℝ) := div_pos Real.pi_pos hnR
  rcases horient with hbc | hda
  · have hgap : b + 2 ≤ c := dangerousRuns_separated hab.1 hcd.1 hbc
    have hgrid :
        Erdos228.Intervals.gridPoint n (b + 1) + Real.pi / n ≤
          Erdos228.Intervals.gridPoint n c := by
      rw [← Erdos228.Intervals.gridPoint_succ]
      exact hmono hgap
    rw [abs_of_nonpos (by linarith [hx.2, hy.1])]
    linarith [hx.2, hy.1]
  · have hgap : d + 2 ≤ a := dangerousRuns_separated hcd.1 hab.1 hda
    have hgrid :
        Erdos228.Intervals.gridPoint n (d + 1) + Real.pi / n ≤
          Erdos228.Intervals.gridPoint n a := by
      rw [← Erdos228.Intervals.gridPoint_succ]
      exact hmono hgap
    rw [abs_of_nonneg (by linarith [hx.1, hy.2])]
    linarith [hx.1, hy.2]

private theorem rudinShapiro_odd_axis_values (k : ℕ) :
    (rudinShapiroP (2 * k + 1)).eval 1 = (2 ^ (k + 1) : ℕ) ∧
    (rudinShapiroQ (2 * k + 1)).eval 1 = 0 ∧
    (rudinShapiroP (2 * k + 1)).eval (-1) = 0 ∧
    (rudinShapiroQ (2 * k + 1)).eval (-1) = (2 ^ (k + 1) : ℕ) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rcases ih with ⟨hP1, hQ1, hPm1, hQm1⟩
      have hs : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
      rw [hs, show (2 * k + 1) + 2 = ((2 * k + 1) + 1) + 1 by omega]
      rw [eval_rudinShapiroP_succ ((2 * k + 1) + 1) 1,
        eval_rudinShapiroQ_succ ((2 * k + 1) + 1) 1,
        eval_rudinShapiroP_succ ((2 * k + 1) + 1) (-1),
        eval_rudinShapiroQ_succ ((2 * k + 1) + 1) (-1)]
      rw [eval_rudinShapiroP_succ (2 * k + 1) 1,
        eval_rudinShapiroQ_succ (2 * k + 1) 1,
        eval_rudinShapiroP_succ (2 * k + 1) (-1),
        eval_rudinShapiroQ_succ (2 * k + 1) (-1)]
      rw [hP1, hQ1, hPm1, hQm1]
      norm_num [pow_succ]
      ring

private theorem sqrt_two_pow_odd_succ (k : ℕ) :
    Real.sqrt (2 ^ ((2 * k + 1) + 1) : ℝ) = (2 ^ (k + 1) : ℕ) := by
  rw [show (2 * k + 1) + 1 = (k + 1) * 2 by omega, pow_mul]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
  · norm_num
  · positivity

theorem normalizedH_re_zero_of_odd {t : ℕ} (ht : Odd t) :
    (normalizedH t 0).re = 1 := by
  obtain ⟨k, rfl⟩ := ht
  rcases rudinShapiro_odd_axis_values k with ⟨hP1, hQ1, _hPm1, _hQm1⟩
  have hunit0 : unitPoint 0 = 1 := by simp [unitPoint]
  simp only [normalizedH, normalizedPDerivative, normalizedQDerivative, pow_zero,
    one_mul, Function.iterate_zero_apply, hunit0, zero_div, rsNormalization]
  rw [hP1, hQ1, sqrt_two_pow_odd_succ]
  norm_num

private theorem unitPoint_evenT_mul_pi (t : ℕ) :
    unitPoint ((evenT t : ℝ) * Real.pi) = 1 := by
  rw [show unitPoint ((evenT t : ℝ) * Real.pi) = unitPoint Real.pi ^ evenT t by
    simp only [unitPoint, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring]
  have hpi : unitPoint Real.pi = -1 := by simp [unitPoint]
  rw [hpi]
  rw [show evenT t = 2 * 2 ^ (t + 9) by simp [evenT, pow_succ']]
  rw [pow_mul]
  norm_num

theorem normalizedH_re_evenT_mul_pi_of_odd {t : ℕ} (ht : Odd t) :
    (normalizedH t ((evenT t : ℝ) * Real.pi)).re = 1 := by
  obtain ⟨k, rfl⟩ := ht
  rcases rudinShapiro_odd_axis_values k with ⟨_hP1, _hQ1, hPm1, hQm1⟩
  have hTpos : (0 : ℝ) < evenT (2 * k + 1) := by
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) ((2 * k + 1) + 10))
  have hdiv :
      ((evenT (2 * k + 1) : ℝ) * Real.pi) / evenT (2 * k + 1) =
        Real.pi := by
    field_simp
  have hphase₁ := unitPoint_evenT_mul_pi (2 * k + 1)
  have hphase₂ :
      unitPoint (2 * ((evenT (2 * k + 1) : ℝ) * Real.pi)) = 1 := by
    rw [show 2 * ((evenT (2 * k + 1) : ℝ) * Real.pi) =
      (evenT (2 * k + 1) : ℝ) * Real.pi +
        (evenT (2 * k + 1) : ℝ) * Real.pi by ring]
    rw [show unitPoint
        ((evenT (2 * k + 1) : ℝ) * Real.pi +
          (evenT (2 * k + 1) : ℝ) * Real.pi) =
        unitPoint ((evenT (2 * k + 1) : ℝ) * Real.pi) *
          unitPoint ((evenT (2 * k + 1) : ℝ) * Real.pi) by
      simp [unitPoint, Complex.exp_add, add_mul]]
    rw [hphase₁]
    norm_num
  simp only [normalizedH, normalizedPDerivative, normalizedQDerivative, pow_zero,
    one_mul, Function.iterate_zero_apply, hphase₁, hphase₂, hdiv,
    show unitPoint Real.pi = -1 by simp [unitPoint], rsNormalization]
  rw [hPm1, hQm1, sqrt_two_pow_odd_succ]
  norm_num

theorem cosineThreshold_lt_half_normalization
    {n t : ℕ} {gamma : ℝ} (hparam : Parameters n t gamma) :
    cosineThreshold n gamma < Real.sqrt (2 ^ (t + 1) : ℝ) / 2 := by
  have hgamma0 : 0 ≤ gamma := (hparam.gamma_pos).le
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hthreshold0 : 0 ≤ cosineThreshold n gamma := by
    exact (cosineThreshold_pos hparam.n_pos hparam.gamma_pos).le
  have hscale0 : 0 < Real.sqrt (2 ^ (t + 1) : ℝ) := by positivity
  have hscaleSq : (Real.sqrt (2 ^ (t + 1) : ℝ)) ^ 2 = 2 ^ (t + 1) :=
    Real.sq_sqrt (by positivity)
  have hthresholdSq :
      (cosineThreshold n gamma) ^ 2 =
        (1 / 2 ^ 16 : ℝ) * (gamma ^ 7 * n) := by
    simp only [cosineThreshold, cosineDelta, mul_pow]
    rw [Real.sq_sqrt hgamma0, Real.sq_sqrt hn0]
    ring
  have hgammaOne : gamma ≤ 1 :=
    hparam.gamma_upper.trans (by norm_num)
  have hgammaPow : gamma ^ 6 ≤ 1 := by
    exact pow_le_one₀ hgamma0 hgammaOne
  have hnum : parameterNumerator t < 2 ^ (t + 12) := by
    have hpowpos : 0 < 2 ^ t := by positivity
    simp only [parameterNumerator, pow_add]
    norm_num
    omega
  have hnumR : (parameterNumerator t : ℝ) < (2 : ℝ) ^ (t + 12) := by
    exact_mod_cast hnum
  have hgammaNum : gamma ^ 7 * (n : ℝ) < (2 : ℝ) ^ (t + 12) := by
    calc
      gamma ^ 7 * (n : ℝ) = gamma ^ 6 * (gamma * n) := by ring
      _ = gamma ^ 6 * parameterNumerator t := by rw [hparam.equation]
      _ ≤ 1 * parameterNumerator t := by
        exact mul_le_mul_of_nonneg_right hgammaPow (by positivity)
      _ < (2 : ℝ) ^ (t + 12) := by simpa using hnumR
  have hsqLt :
      (cosineThreshold n gamma) ^ 2 <
        (Real.sqrt (2 ^ (t + 1) : ℝ) / 2) ^ 2 := by
    rw [hthresholdSq, div_pow, hscaleSq]
    calc
      (1 / 2 ^ 16 : ℝ) * (gamma ^ 7 * n) <
          (1 / 2 ^ 16 : ℝ) * 2 ^ (t + 12) := by gcongr
      _ < (2 ^ (t + 1) : ℝ) / 2 ^ 2 := by
        norm_num [pow_add]
        have hpow : (0 : ℝ) < 2 ^ t := by positivity
        nlinarith
  nlinarith

private theorem normalizedH_re_gt_half_of_close
    {t : ℕ} {axis x : ℝ}
    (haxis : (normalizedH t axis).re = 1)
    (hdiff : Differentiable ℝ (fun y ↦ (normalizedH t y).re))
    (hderiv : ∀ y,
      |iteratedDeriv 1 (fun z ↦ (normalizedH t z).re) y| ≤ 18)
    (hclose : 18 * |x - axis| < 1 / 2) :
    1 / 2 < (normalizedH t x).re := by
  have hmean :
      |(normalizedH t x).re - (normalizedH t axis).re| ≤
        18 * |x - axis| := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (s := Set.univ) (f := fun y ↦ (normalizedH t y).re)
      (x := axis) (y := x)
      (fun y _ ↦ hdiff.differentiableAt)
      (fun y _ ↦ by
        simpa only [Real.norm_eq_abs, iteratedDeriv_succ', iteratedDeriv_zero]
          using hderiv y)
      convex_univ (Set.mem_univ axis) (Set.mem_univ x)
    simpa only [Real.norm_eq_abs, abs_sub_comm] using h
  rw [haxis] at hmean
  have := (abs_le.mp hmean).1
  linarith

private theorem two_mul_evenT_div_n_lt_gamma
    {n t : ℕ} {gamma : ℝ} (hparam : Parameters n t gamma) :
    (2 * evenT t : ℝ) / n < gamma := by
  obtain ⟨k, ht⟩ := hparam.t_odd
  have htpos : 0 < t := by omega
  have hpow : 1 < 2 ^ t := by
    exact one_lt_pow₀ (by norm_num) htpos.ne'
  have hnat : 2 * evenT t < parameterNumerator t := by
    rw [parameterNumerator, two_mul_evenT]
    omega
  have hreal : (2 * evenT t : ℝ) < gamma * n := by
    rw [hparam.equation]
    exact_mod_cast hnat
  have hnR : (0 : ℝ) < n := by exact_mod_cast hparam.n_pos
  exact (div_lt_iff₀ hnR).2 hreal

private theorem axis_close_numeric
    {n t : ℕ} {gamma : ℝ} (hparam : Parameters n t gamma)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : C ≤ 101) :
    18 * C * Real.pi * ((2 * evenT t : ℝ) / n) < 1 / 2 := by
  have hratio := two_mul_evenT_div_n_lt_gamma hparam
  have hgamma0 := hparam.gamma_pos.le
  calc
    18 * C * Real.pi * ((2 * evenT t : ℝ) / n) ≤
        18 * C * Real.pi * gamma := by
      apply mul_le_mul_of_nonneg_left hratio.le
      positivity
    _ ≤ 18 * 101 * 4 * (1 / 2 ^ 40 : ℝ) := by
      gcongr
      · exact Real.pi_le_four
      · exact hparam.gamma_upper
    _ < 1 / 2 := by norm_num

theorem not_badCell_of_left_axis
    {n t i : ℕ} {gamma : ℝ} (hparam : Parameters n t gamma)
    (hdiff : Differentiable ℝ (fun y ↦ (normalizedH t y).re))
    (hderiv : ∀ y,
      |iteratedDeriv 1 (fun z ↦ (normalizedH t z).re) y| ≤ 18)
    (hi : i < 100) :
    ¬BadCell n t gamma i := by
  rintro ⟨theta, htheta, hsmall⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hparam.n_pos
  have hmono := Erdos228.Intervals.gridPoint_mono hparam.n_pos
  have htheta0 : 0 ≤ theta := by
    have hgp : 0 ≤ Erdos228.Intervals.gridPoint n i := by
      rw [← Erdos228.Intervals.gridPoint_zero n]
      exact hmono (Nat.zero_le i)
    exact hgp.trans htheta.1
  have htheta100 : theta ≤ 100 * Real.pi / n := by
    calc
      theta ≤ Erdos228.Intervals.gridPoint n (i + 1) := htheta.2
      _ ≤ Erdos228.Intervals.gridPoint n 100 := hmono (by omega)
      _ = 100 * Real.pi / n := by simp [Erdos228.Intervals.gridPoint]
  let x : ℝ := 2 * evenT t * theta
  have hxclose : 18 * |x - 0| < 1 / 2 := by
    have hT0 : (0 : ℝ) ≤ 2 * evenT t := by positivity
    rw [sub_zero, abs_of_nonneg (mul_nonneg hT0 htheta0)]
    calc
      18 * (2 * (evenT t : ℝ) * theta) ≤
          18 * (2 * (evenT t : ℝ) * (100 * Real.pi / n)) := by gcongr
      _ = 18 * 100 * Real.pi * ((2 * evenT t : ℝ) / n) := by ring
      _ < 1 / 2 := axis_close_numeric hparam (by norm_num) (by norm_num)
  have hxhalf : 1 / 2 < (normalizedH t x).re :=
    normalizedH_re_gt_half_of_close
      (normalizedH_re_zero_of_odd hparam.t_odd) hdiff hderiv hxclose
  have hscale : 0 < Real.sqrt (2 ^ (t + 1) : ℝ) := by positivity
  have hthreshold := cosineThreshold_lt_half_normalization hparam
  have hcos : cosineThreshold n gamma < evenCosine t theta := by
    rw [evenCosine_eq_normalizedH]
    change cosineThreshold n gamma <
      Real.sqrt (2 ^ (t + 1) : ℝ) * (normalizedH t x).re
    nlinarith
  have habs : evenCosine t theta ≤ |evenCosine t theta| := le_abs_self _
  linarith

theorem not_badCell_of_right_axis
    {n t i : ℕ} {gamma : ℝ} (hparam : Parameters n t gamma)
    (hdiff : Differentiable ℝ (fun y ↦ (normalizedH t y).re))
    (hderiv : ∀ y,
      |iteratedDeriv 1 (fun z ↦ (normalizedH t z).re) y| ≤ 18)
    (hiFirst : 2 * (i + 1) ≤ n)
    (hiNear : ¬2 * (i + 1 + 100) ≤ n) :
    ¬BadCell n t gamma i := by
  rintro ⟨theta, htheta, hsmall⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hparam.n_pos
  have hiFirstR : (2 : ℝ) * (i + 1) ≤ n := by exact_mod_cast hiFirst
  have hiNearNat : n < 2 * (i + 101) := by omega
  have hiNearR : (n : ℝ) < 2 * (i + 101) := by exact_mod_cast hiNearNat
  have hrightEndpoint :
      Erdos228.Intervals.gridPoint n (i + 1) ≤ Real.pi / 2 := by
    simp only [Erdos228.Intervals.gridPoint, Nat.cast_add, Nat.cast_one]
    apply (div_le_iff₀ hnR).2
    field_simp [hnR.ne']
    nlinarith [Real.pi_pos]
  have hthetaAxis : theta ≤ Real.pi / 2 :=
    htheta.2.trans hrightEndpoint
  have hgridDist :
      Real.pi / 2 - Erdos228.Intervals.gridPoint n i <
        101 * Real.pi / n := by
    simp only [Erdos228.Intervals.gridPoint]
    apply (sub_lt_iff_lt_add).2
    rw [← add_div]
    apply (lt_div_iff₀ hnR).2
    nlinarith [Real.pi_pos]
  have hthetaDist : Real.pi / 2 - theta < 101 * Real.pi / n := by
    linarith [htheta.1, hgridDist]
  have hthetaDist0 : 0 ≤ Real.pi / 2 - theta := sub_nonneg.mpr hthetaAxis
  let x : ℝ := 2 * evenT t * theta
  let axis : ℝ := evenT t * Real.pi
  have hxclose : 18 * |x - axis| < 1 / 2 := by
    have hT0 : (0 : ℝ) ≤ 2 * evenT t := by positivity
    rw [show x - axis =
        -(2 * (evenT t : ℝ)) * (Real.pi / 2 - theta) by
      dsimp only [x, axis]
      ring]
    rw [abs_mul, abs_neg, abs_of_nonneg hT0, abs_of_nonneg hthetaDist0]
    calc
      18 * (2 * (evenT t : ℝ) * (Real.pi / 2 - theta)) ≤
          18 * (2 * (evenT t : ℝ) * (101 * Real.pi / n)) := by
            gcongr
      _ = 18 * 101 * Real.pi * ((2 * evenT t : ℝ) / n) := by ring
      _ < 1 / 2 := axis_close_numeric hparam (by norm_num) (by norm_num)
  have hxhalf : 1 / 2 < (normalizedH t x).re :=
    normalizedH_re_gt_half_of_close
      (show (normalizedH t axis).re = 1 by
        dsimp only [axis]
        exact normalizedH_re_evenT_mul_pi_of_odd hparam.t_odd)
      hdiff hderiv hxclose
  have hscale : 0 < Real.sqrt (2 ^ (t + 1) : ℝ) := by positivity
  have hthreshold := cosineThreshold_lt_half_normalization hparam
  have hcos : cosineThreshold n gamma < evenCosine t theta := by
    rw [evenCosine_eq_normalizedH]
    change cosineThreshold n gamma <
      Real.sqrt (2 ^ (t + 1) : ℝ) * (normalizedH t x).re
    nlinarith
  have habs : evenCosine t theta ≤ |evenCosine t theta| := le_abs_self _
  linarith

/-- The grid cell whose left endpoint is indexed by `n / 2` meets the
middle axis `pi / 2`, and is therefore good.  This includes the cell which
straddles the axis when `n` is odd. -/
theorem not_badCell_middle_axis
    {n t : ℕ} {gamma : ℝ} (hparam : Parameters n t gamma)
    (hdiff : Differentiable ℝ (fun y ↦ (normalizedH t y).re))
    (hderiv : ∀ y,
      |iteratedDeriv 1 (fun z ↦ (normalizedH t z).re) y| ≤ 18) :
    ¬BadCell n t gamma (n / 2) := by
  rintro ⟨theta, htheta, hsmall⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hparam.n_pos
  have hqLower : 2 * (n / 2) ≤ n := by omega
  have hqUpper : n < 2 * (n / 2 + 1) := by omega
  have hqLowerR : (2 : ℝ) * ((n / 2 : ℕ) : ℝ) ≤ n := by
    exact_mod_cast hqLower
  have hqUpperR : (n : ℝ) < 2 * (((n / 2 : ℕ) : ℝ) + 1) := by
    exact_mod_cast hqUpper
  have hgridLower :
      Real.pi / 2 - Real.pi / n ≤
        Erdos228.Intervals.gridPoint n (n / 2) := by
    simp only [Erdos228.Intervals.gridPoint]
    field_simp [hnR.ne']
    nlinarith [Real.pi_pos]
  have hgridUpper :
      Erdos228.Intervals.gridPoint n (n / 2 + 1) ≤
        Real.pi / 2 + Real.pi / n := by
    simp only [Erdos228.Intervals.gridPoint, Nat.cast_add, Nat.cast_one]
    field_simp [hnR.ne']
    nlinarith [Real.pi_pos]
  have hthetaDist : |theta - Real.pi / 2| ≤ Real.pi / n := by
    rw [abs_le]
    constructor <;> linarith [htheta.1, htheta.2, hgridLower, hgridUpper]
  let x : ℝ := 2 * evenT t * theta
  let axis : ℝ := evenT t * Real.pi
  have hxclose : 18 * |x - axis| < 1 / 2 := by
    have hT0 : (0 : ℝ) ≤ 2 * evenT t := by positivity
    rw [show x - axis =
        (2 * (evenT t : ℝ)) * (theta - Real.pi / 2) by
      dsimp only [x, axis]
      ring]
    rw [abs_mul, abs_of_nonneg hT0]
    calc
      18 * (2 * (evenT t : ℝ) * |theta - Real.pi / 2|) ≤
          18 * (2 * (evenT t : ℝ) * (Real.pi / n)) := by gcongr
      _ = 18 * 1 * Real.pi * ((2 * evenT t : ℝ) / n) := by ring
      _ < 1 / 2 := axis_close_numeric hparam (by norm_num) (by norm_num)
  have hxhalf : 1 / 2 < (normalizedH t x).re :=
    normalizedH_re_gt_half_of_close
      (show (normalizedH t axis).re = 1 by
        dsimp only [axis]
        exact normalizedH_re_evenT_mul_pi_of_odd hparam.t_odd)
      hdiff hderiv hxclose
  have hscale : 0 < Real.sqrt (2 ^ (t + 1) : ℝ) := by positivity
  have hthreshold := cosineThreshold_lt_half_normalization hparam
  have hcos : cosineThreshold n gamma < evenCosine t theta := by
    rw [evenCosine_eq_normalizedH]
    change cosineThreshold n gamma <
      Real.sqrt (2 ^ (t + 1) : ℝ) * (normalizedH t x).re
    nlinarith
  have habs : evenCosine t theta ≤ |evenCosine t theta| := le_abs_self _
  linarith

/-- Once the local large-value argument excludes bad cells next to the two
first-quadrant axes, the endpoint margin is pure grid arithmetic. -/
theorem firstQuadrantIntervals_away_from_axes_of_badCell_exclusion
    {n t : ℕ} {gamma : ℝ} (hn : 0 < n)
    (hleft : ∀ i, i < 100 → ¬BadCell n t gamma i)
    (hright : ∀ i, 2 * (i + 1) ≤ n → ¬2 * (i + 1 + 100) ≤ n →
      ¬BadCell n t gamma i) :
    ∀ I ∈ firstQuadrantIntervals n t gamma,
      100 * Real.pi / n ≤ I.1 ∧
        I.2 ≤ Real.pi / 2 - 100 * Real.pi / n := by
  classical
  intro I hI
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hI
  rw [mem_firstQuadrantRuns] at hab
  have hrun :
      Erdos228.Intervals.IsMaximalBadRun (2 * n) (BadCell n t gamma) a b := by
    simpa only [mem_dangerousRuns] using hab.1
  have hbada : BadCell n t gamma a :=
    hrun.2.2.1 a (Finset.mem_range.mpr (hrun.1.trans_lt hrun.2.1)) le_rfl hrun.1
  have hbadb : BadCell n t gamma b :=
    hrun.2.2.1 b (Finset.mem_range.mpr hrun.2.1) hrun.1 le_rfl
  have ha100 : 100 ≤ a := by
    by_contra ha
    exact hleft a (by omega) hbada
  have hb100 : 2 * (b + 1 + 100) ≤ n := by
    by_contra hb
    exact hright b hab.2 hb hbadb
  simp only [runEndpoints]
  constructor
  · rw [show 100 * Real.pi / (n : ℝ) =
        Erdos228.Intervals.gridPoint n 100 by
      simp [Erdos228.Intervals.gridPoint]]
    exact Erdos228.Intervals.gridPoint_mono hn ha100
  · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hb100R : (2 : ℝ) * (b + 1 + 100) ≤ n := by exact_mod_cast hb100
    simp only [Erdos228.Intervals.gridPoint, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat]
    apply (div_le_iff₀ hnR).2
    field_simp [hnR.ne']
    nlinarith [Real.pi_pos]

/-- The finite-grid separation and axis-exclusion conclusions assemble the
geometric certificate without any further analytic input. -/
theorem geometricCertificateOfBadCellExclusion
    {n t : ℕ} {gamma : ℝ} (hn : 0 < n)
    (hleft : ∀ i, i < 100 → ¬BadCell n t gamma i)
    (hright : ∀ i, 2 * (i + 1) ≤ n → ¬2 * (i + 1 + 100) ≤ n →
      ¬BadCell n t gamma i) :
    GeometricCertificate n t gamma where
  separated := firstQuadrantIntervals_pairwise_separated hn
  away_from_axes :=
    firstQuadrantIntervals_away_from_axes_of_badCell_exclusion hn hleft hright

theorem geometricCertificate_of_parameters
    {n t : ℕ} {gamma : ℝ} (hparam : Parameters n t gamma) :
    GeometricCertificate n t gamma := by
  have hdiff : Differentiable ℝ (fun y ↦ (normalizedH t y).re) :=
    (contDiff_normalizedH_re t).differentiable (by norm_num)
  have hderiv : ∀ y,
      |iteratedDeriv 1 (fun z ↦ (normalizedH t z).re) y| ≤ 18 := by
    intro y
    exact abs_iteratedDeriv_normalizedH_re_le_eighteen 1 (by omega) t y
  apply geometricCertificateOfBadCellExclusion hparam.n_pos
  · intro i hi
    exact not_badCell_of_left_axis hparam hdiff hderiv hi
  · intro i hiFirst hiNear
    exact not_badCell_of_right_axis hparam hdiff hderiv hiFirst hiNear

/-- Every first-quadrant point where the cosine is below its target level is
covered by one of the maximal bad intervals retained in the first quadrant.
The middle-axis large-value cell ensures that the containing maximal run
cannot cross `pi / 2`. -/
theorem low_point_covered_by_firstQuadrantIntervals
    {n t : ℕ} {gamma theta : ℝ} (hparam : Parameters n t gamma)
    (htheta : theta ∈ Icc 0 (Real.pi / 2))
    (hsmall : |evenCosine t theta| < cosineThreshold n gamma) :
    ∃ I ∈ firstQuadrantIntervals n t gamma,
      Erdos228.OddSine.InInterval I theta := by
  classical
  have hdiff : Differentiable ℝ (fun y ↦ (normalizedH t y).re) :=
    (contDiff_normalizedH_re t).differentiable (by norm_num)
  have hderiv : ∀ y,
      |iteratedDeriv 1 (fun z ↦ (normalizedH t z).re) y| ≤ 18 := by
    intro y
    exact abs_iteratedDeriv_normalizedH_re_le_eighteen 1 (by omega) t y
  have hnR : (0 : ℝ) < n := by exact_mod_cast hparam.n_pos
  let P : ℕ → Prop := fun k ↦
    theta ≤ Erdos228.Intervals.gridPoint n (k + 1)
  have hqUpper : n < 2 * (n / 2 + 1) := by omega
  have hqUpperR : (n : ℝ) < 2 * (((n / 2 : ℕ) : ℝ) + 1) := by
    exact_mod_cast hqUpper
  have haxisGrid :
      Real.pi / 2 ≤ Erdos228.Intervals.gridPoint n (n / 2 + 1) := by
    simp only [Erdos228.Intervals.gridPoint, Nat.cast_add, Nat.cast_one]
    field_simp [hnR.ne']
    nlinarith [Real.pi_pos]
  have hPex : ∃ k, P k :=
    ⟨n / 2, htheta.2.trans haxisGrid⟩
  let i : ℕ := Nat.find hPex
  have hiright : theta ≤ Erdos228.Intervals.gridPoint n (i + 1) := by
    simpa only [i, P] using Nat.find_spec hPex
  have hileft : Erdos228.Intervals.gridPoint n i ≤ theta := by
    by_cases hi0 : i = 0
    · rw [hi0, Erdos228.Intervals.gridPoint_zero]
      exact htheta.1
    · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
      have hnot := Nat.find_min hPex (show i - 1 < Nat.find hPex by
        simpa only [i] using Nat.sub_lt hipos Nat.one_pos)
      have hpred : i - 1 + 1 = i := by omega
      change ¬theta ≤ Erdos228.Intervals.gridPoint n (i - 1 + 1) at hnot
      rw [hpred] at hnot
      exact (lt_of_not_ge hnot).le
  have hiq : i ≤ n / 2 := by
    exact Nat.find_min' hPex (htheta.2.trans haxisGrid)
  have hiN : i < 2 * n := by
    have hnpos : 0 < n := hparam.n_pos
    have hn2 : n < 2 * n := by omega
    exact hiq.trans_lt ((Nat.div_le_self n 2).trans_lt hn2)
  have hbad : BadCell n t gamma i :=
    ⟨theta, ⟨hileft, hiright⟩, hsmall⟩
  obtain ⟨⟨a, b⟩, hab, hai, hib⟩ :=
    Erdos228.Intervals.exists_mem_maximalBadRuns_containing hiN hbad
  have hrun : (a, b) ∈ dangerousRuns n t gamma := by
    simpa only [dangerousRuns] using hab
  have hfirst : 2 * (b + 1) ≤ n := by
    by_contra hcross
    have hqLower : 2 * (n / 2) ≤ n := by omega
    have haq : a ≤ n / 2 := hai.trans hiq
    have hqb : n / 2 ≤ b := by omega
    have hmax :
        Erdos228.Intervals.IsMaximalBadRun
          (2 * n) (BadCell n t gamma) a b :=
      mem_dangerousRuns.mp hrun
    have hbadMiddle : BadCell n t gamma (n / 2) :=
      hmax.2.2.1 (n / 2)
        (Finset.mem_range.mpr (by omega)) haq hqb
    exact not_badCell_middle_axis hparam hdiff hderiv hbadMiddle
  have hfirstRun : (a, b) ∈ firstQuadrantRuns n t gamma :=
    mem_firstQuadrantRuns.mpr ⟨hrun, hfirst⟩
  refine ⟨runEndpoints n (a, b), ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨(a, b), hfirstRun, rfl⟩
  · simp only [Erdos228.OddSine.InInterval, runEndpoints, mem_Icc]
    have hmono := Erdos228.Intervals.gridPoint_mono hparam.n_pos
    exact ⟨(hmono hai).trans hileft,
      hiright.trans (hmono (by omega))⟩

end

end Erdos228.CosineConstruction
