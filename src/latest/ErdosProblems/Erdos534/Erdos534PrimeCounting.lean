import ErdosProblems.Erdos534.Erdos534Core

namespace Erdos534

open Real

private lemma intervalIntegrable_inv_log_sq {a b : ℝ} (hab : a ≤ b) (ha : 1 < a) :
    IntervalIntegrable (fun x : ℝ ↦ 1 / log x ^ 2) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  rw [Set.uIcc_of_le hab] at hx
  have hx1 : 1 < x := lt_of_lt_of_le ha hx.1
  have hx0 : x ≠ 0 := by linarith
  have hlog0 : log x ^ 2 ≠ 0 := pow_ne_zero _
    (log_ne_zero.mpr ⟨hx0, ne_of_gt hx1, by linarith⟩)
  exact (continuousAt_const.div ((continuousAt_log hx0).pow 2) hlog0).continuousWithinAt

lemma integral_inv_log_sq_le_const {a b L : ℝ}
    (hab : a ≤ b) (ha : 1 < a) (hL : 0 < L) (hlog : L ≤ log a) :
    (∫ x in a..b, 1 / log x ^ 2) ≤ (b - a) / L ^ 2 := by
  calc
    (∫ x in a..b, 1 / log x ^ 2) ≤ ∫ _x in a..b, 1 / L ^ 2 := by
      apply intervalIntegral.integral_mono_on hab
      · exact intervalIntegrable_inv_log_sq hab ha
      · exact intervalIntegrable_const
      · intro x hx
        have hxpos : 0 < x := lt_trans (by norm_num) (lt_of_lt_of_le ha hx.1)
        have hloga : log a ≤ log x := log_le_log (by linarith) hx.1
        have hlogx : 0 < log x := log_pos (lt_of_lt_of_le ha hx.1)
        apply one_div_le_one_div_of_le (sq_pos_of_pos hL)
        nlinarith [sq_le_sq₀ hL.le hlogx.le |>.2 (hlog.trans hloga)]
    _ = (b - a) / L ^ 2 := by simp [div_eq_mul_inv]

lemma log_thirty_lower : (17 / 5 : ℝ) < log 30 := by
  rw [show (30 : ℝ) = 6 * 5 by norm_num,
    log_mul (by norm_num : (6 : ℝ) ≠ 0) (by norm_num),
    show (6 : ℝ) = 2 * 3 by norm_num,
    log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num)]
  nlinarith [Real.log_two_gt_d9, Real.log_three_gt_d9, Real.log_five_gt_d9]

lemma log_two_lower : (69 / 100 : ℝ) < log 2 := by
  nlinarith [Real.log_two_gt_d9]

lemma log_10000_upper : log (10000 : ℝ) < (1152 / 125 : ℝ) := by
  rw [ElementaryChebyshev.log_10000_eq]
  nlinarith [Real.log_two_lt_d9, Real.log_five_lt_d9]

lemma integral_inv_log_sq_30_10000 :
    (∫ x in (30 : ℝ)..10000, 1 / log x ^ 2) ≤ 173 := by
  have hseg (i : ℕ) (hi : i ≤ 7) :
      (∫ x in (30 * 2 ^ i : ℝ)..(30 * 2 ^ (i + 1) : ℝ),
          1 / log x ^ 2) ≤
        (30 * 2 ^ (i + 1) - 30 * 2 ^ i) /
          ((17 / 5 : ℝ) + i * (69 / 100 : ℝ)) ^ 2 := by
    apply integral_inv_log_sq_le_const
    · rw [pow_succ]
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) i]
    · have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ i := one_le_pow₀ (by norm_num)
      nlinarith
    · positivity
    · rw [show (30 * 2 ^ i : ℝ) = 30 * (2 : ℝ) ^ i by norm_num,
        log_mul (by norm_num) (by positivity), log_pow]
      have h30 := log_thirty_lower.le
      have h2 := log_two_lower.le
      nlinarith
  have hlast :
      (∫ x in (7680 : ℝ)..10000, 1 / log x ^ 2) ≤
        (10000 - 7680) / ((17 / 5 : ℝ) + 8 * (69 / 100 : ℝ)) ^ 2 := by
    apply integral_inv_log_sq_le_const <;> try norm_num
    rw [show (7680 : ℝ) = 30 * (2 : ℝ) ^ 8 by norm_num,
      log_mul (by norm_num) (by norm_num), log_pow]
    nlinarith [log_thirty_lower, log_two_lower]
  have hsplit :
      (∫ x in (30 : ℝ)..10000, 1 / log x ^ 2) =
        (∫ x in (30 : ℝ)..60, 1 / log x ^ 2) +
        (∫ x in (60 : ℝ)..120, 1 / log x ^ 2) +
        (∫ x in (120 : ℝ)..240, 1 / log x ^ 2) +
        (∫ x in (240 : ℝ)..480, 1 / log x ^ 2) +
        (∫ x in (480 : ℝ)..960, 1 / log x ^ 2) +
        (∫ x in (960 : ℝ)..1920, 1 / log x ^ 2) +
        (∫ x in (1920 : ℝ)..3840, 1 / log x ^ 2) +
        (∫ x in (3840 : ℝ)..7680, 1 / log x ^ 2) +
        (∫ x in (7680 : ℝ)..10000, 1 / log x ^ 2) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (b := 60),
      intervalIntegral.integral_add_adjacent_intervals (b := 120),
      intervalIntegral.integral_add_adjacent_intervals (b := 240),
      intervalIntegral.integral_add_adjacent_intervals (b := 480),
      intervalIntegral.integral_add_adjacent_intervals (b := 960),
      intervalIntegral.integral_add_adjacent_intervals (b := 1920),
      intervalIntegral.integral_add_adjacent_intervals (b := 3840),
      intervalIntegral.integral_add_adjacent_intervals (b := 7680)]
    all_goals apply intervalIntegrable_inv_log_sq <;> norm_num
  rw [hsplit]
  have h0 := hseg 0 (by omega)
  have h1 := hseg 1 (by omega)
  have h2 := hseg 2 (by omega)
  have h3 := hseg 3 (by omega)
  have h4 := hseg 4 (by omega)
  have h5 := hseg 5 (by omega)
  have h6 := hseg 6 (by omega)
  have h7 := hseg 7 (by omega)
  norm_num at h0 h1 h2 h3 h4 h5 h6 h7 hlast ⊢
  linarith

noncomputable def invLogSquareMajorant (x : ℝ) : ℝ :=
  (3 / 2 : ℝ) * x / log x ^ 2

lemma invLogSquareMajorant_10000 :
    173 ≤ invLogSquareMajorant 10000 := by
  have hlogpos : 0 < log (10000 : ℝ) := log_pos (by norm_num)
  have hlog := log_10000_upper
  rw [invLogSquareMajorant]
  apply (le_div_iff₀ (sq_pos_of_pos hlogpos)).2
  nlinarith [sq_lt_sq₀ hlogpos.le (by linarith : 0 ≤ (1152 / 125 : ℝ)) |>.2 hlog]

lemma hasDerivAt_invLogSquareMajorant {x : ℝ} (hx : 1 < x) :
    HasDerivAt invLogSquareMajorant
      ((3 / 2 : ℝ) * (log x - 2) / log x ^ 3) x := by
  have hx0 : x ≠ 0 := by linarith
  have hlog0 : log x ≠ 0 :=
    log_ne_zero.mpr ⟨hx0, ne_of_gt hx, by linarith⟩
  have h := ((hasDerivAt_id x).const_mul (3 / 2 : ℝ)).div
    ((hasDerivAt_log hx0).pow 2) (pow_ne_zero _ hlog0)
  have hfun : invLogSquareMajorant =
      (fun y : ℝ => (3 / 2 : ℝ) * y) / log ^ 2 := by
    funext y
    rfl
  rw [hfun]
  have hraw : HasDerivAt ((fun y : ℝ => (3 / 2 : ℝ) * y) / log ^ 2)
      (((3 / 2 : ℝ) * log x ^ 2 -
          (3 / 2 : ℝ) * x * (2 * log x * x⁻¹)) / (log x ^ 2) ^ 2) x := by
    simpa only [id_eq, one_mul, mul_one, Nat.cast_ofNat, Nat.reduceSub, pow_one,
      Pi.pow_apply] using h
  have hval :
      (((3 / 2 : ℝ) * log x ^ 2 -
          (3 / 2 : ℝ) * x * (2 * log x * x⁻¹)) / (log x ^ 2) ^ 2) =
        (3 / 2 : ℝ) * (log x - 2) / log x ^ 3 := by
    field_simp [hlog0]
  rw [← hval]
  exact hraw

lemma inv_log_sq_le_deriv_majorant {x : ℝ} (hx : 10000 ≤ x) :
    1 / log x ^ 2 ≤ (3 / 2 : ℝ) * (log x - 2) / log x ^ 3 := by
  have hlogbase : 8 < log (10000 : ℝ) := by
    rw [ElementaryChebyshev.log_10000_eq]
    nlinarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  have hlogmono : log (10000 : ℝ) ≤ log x :=
    log_le_log (by norm_num) hx
  have hlog : 8 < log x := hlogbase.trans_le hlogmono
  have hcube : 0 < log x ^ 3 := pow_pos (by linarith) _
  apply (le_div_iff₀ hcube).2
  field_simp [ne_of_gt (by linarith : 0 < log x)]
  nlinarith

lemma integral_inv_log_sq_majorized {x : ℝ} (hx : 10000 ≤ x) :
    (∫ t in (30 : ℝ)..x, 1 / log t ^ 2) ≤ invLogSquareMajorant x := by
  have hIntBase := integral_inv_log_sq_30_10000
  have hGBase := invLogSquareMajorant_10000
  have hTail : (∫ t in (10000 : ℝ)..x, 1 / log t ^ 2) ≤
      invLogSquareMajorant x - invLogSquareMajorant 10000 := by
    apply intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hx
    · intro t ht
      exact (hasDerivAt_invLogSquareMajorant (by linarith [ht.1])).continuousAt.continuousWithinAt
    · intro t ht
      exact (hasDerivAt_invLogSquareMajorant (by linarith [ht.1])).hasDerivWithinAt
    · apply ContinuousOn.integrableOn_Icc
      intro t ht
      have ht1 : 1 < t := by linarith [ht.1]
      have ht0 : t ≠ 0 := by linarith
      have hlog0 : log t ^ 2 ≠ 0 := pow_ne_zero _
        (log_ne_zero.mpr ⟨ht0, ne_of_gt ht1, by linarith⟩)
      exact (continuousAt_const.div ((continuousAt_log ht0).pow 2) hlog0).continuousWithinAt
    · intro t ht
      exact inv_log_sq_le_deriv_majorant ht.1.le
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_inv_log_sq (by norm_num) (by norm_num))
    (intervalIntegrable_inv_log_sq hx (by norm_num))]
  linarith

lemma integral_theta_2_30_le_ten :
    (∫ t in (2 : ℝ)..30, Chebyshev.theta t / (t * log t ^ 2)) ≤ 10 := by
  have h := Chebyshev.primeCounting_eq_theta_div_log_add_integral
    (x := (30 : ℝ)) (by norm_num)
  have htheta : 0 ≤ Chebyshev.theta (30 : ℝ) / log 30 :=
    div_nonneg (Chebyshev.theta_nonneg _) (log_nonneg (by norm_num))
  have hp : Nat.primeCounting 30 = 10 := by decide
  norm_num only [Nat.floor_natCast] at h
  rw [hp] at h
  norm_num at h
  linarith

lemma theta_integrand_le {t : ℝ} (ht : 30 ≤ t) :
    Chebyshev.theta t / (t * log t ^ 2) ≤
      (111 / 100 : ℝ) * (1 / log t ^ 2) + 5 * (1 / t) := by
  have htpos : 0 < t := by linarith
  have hlog : 0 < log t := log_pos (by linarith)
  have hden : 0 < t * log t ^ 2 := mul_pos htpos (sq_pos_of_pos hlog)
  apply (div_le_iff₀ hden).2
  calc
    Chebyshev.theta t ≤ Chebyshev.psi t := Chebyshev.theta_le_psi t
    _ ≤ (111 / 100 : ℝ) * t + 5 * log t ^ 2 :=
      ElementaryChebyshev.psi_upper_simple t ht
    _ = ((111 / 100 : ℝ) * (1 / log t ^ 2) + 5 * (1 / t)) *
        (t * log t ^ 2) := by
      field_simp

lemma integral_theta_30_upper {x : ℝ} (hx : 30 ≤ x) :
    (∫ t in (30 : ℝ)..x, Chebyshev.theta t / (t * log t ^ 2)) ≤
      (111 / 100 : ℝ) * (∫ t in (30 : ℝ)..x, 1 / log t ^ 2) +
        5 * log (x / 30) := by
  have hthetaInt : IntervalIntegrable
      (fun t : ℝ => Chebyshev.theta t / (t * log t ^ 2))
      MeasureTheory.volume 30 x := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
    exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq x).mono_set (by
      intro t ht
      exact ⟨by linarith [ht.1], ht.2⟩)
  have hInvLog : IntervalIntegrable (fun t : ℝ => 1 / log t ^ 2)
      MeasureTheory.volume 30 x := intervalIntegrable_inv_log_sq hx (by norm_num)
  have hInv : IntervalIntegrable (fun t : ℝ => 1 / t)
      MeasureTheory.volume 30 x := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    exact (continuousAt_const.div continuousAt_id (by
      simp only [id_eq]
      linarith [ht.1])).continuousWithinAt
  calc
    (∫ t in (30 : ℝ)..x, Chebyshev.theta t / (t * log t ^ 2)) ≤
        ∫ t in (30 : ℝ)..x,
          ((111 / 100 : ℝ) * (1 / log t ^ 2) + 5 * (1 / t)) := by
      apply intervalIntegral.integral_mono_on hx hthetaInt (hInvLog.const_mul _ |>.add <|
        hInv.const_mul _)
      intro t ht
      exact theta_integrand_le ht.1
    _ = (111 / 100 : ℝ) * (∫ t in (30 : ℝ)..x, 1 / log t ^ 2) +
          5 * (∫ t in (30 : ℝ)..x, 1 / t) := by
      rw [intervalIntegral.integral_add (hInvLog.const_mul _) (hInv.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ = (111 / 100 : ℝ) * (∫ t in (30 : ℝ)..x, 1 / log t ^ 2) +
          5 * log (x / 30) := by
      rw [integral_one_div_of_pos (by norm_num) (by linarith)]

lemma psi_upper_sharp {x : ℝ} (hx : 30 ≤ x) :
    Chebyshev.psi x ≤ (27639 / 25000 : ℝ) * x +
      (5000 / 1791 : ℝ) * log x ^ 2 := by
  have hxpos : 0 < x := by linarith
  have hx5 : 0 < x / 5 := by positivity
  have hlogx : 0 < log x := log_pos (by linarith)
  have hlog6 : (1791 / 1000 : ℝ) < log 6 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, log_mul (by norm_num) (by norm_num)]
    nlinarith [Real.log_two_gt_d9, Real.log_three_gt_d9]
  have hlogDiv0 : 0 ≤ log (x / 5) := log_nonneg (by linarith)
  have hlogDiv : log (x / 5) ≤ log x :=
    log_le_log hx5 (div_le_self hxpos.le (by norm_num))
  have hquot : log (x / 5) / log 6 ≤ (1000 / 1791 : ℝ) * log x := by
    apply (div_le_iff₀ (by linarith : 0 < log 6)).2
    nlinarith [mul_le_mul_of_nonneg_left hlog6.le hlogx.le]
  have hfactor0 : 0 ≤ 5 * log x - 5 := by
    have hlog3 : 1 < log (3 : ℝ) := by nlinarith [Real.log_three_gt_d9]
    have : 1 < log x := hlog3.trans_le (log_le_log (by norm_num) (by linarith))
    linarith
  have herror :
      (log (x / 5) / log 6) * (5 * log x - 5) ≤
        (5000 / 1791 : ℝ) * log x ^ 2 := by
    calc
      (log (x / 5) / log 6) * (5 * log x - 5) ≤
          ((1000 / 1791 : ℝ) * log x) * (5 * log x - 5) :=
        mul_le_mul_of_nonneg_right hquot hfactor0
      _ ≤ ((1000 / 1791 : ℝ) * log x) * (5 * log x) := by
        gcongr
        norm_num
      _ = (5000 / 1791 : ℝ) * log x ^ 2 := by ring
  nlinarith [ElementaryChebyshev.psi_upper x hx, ElementaryChebyshev.a_bound.2]

lemma primeCounting_upper_large {x : ℝ} (hx : 10000 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤
      (27639 / 25000 : ℝ) * x / log x +
      (333 / 200 : ℝ) * x / log x ^ 2 +
      (13955 / 1791 : ℝ) * log x + 10 := by
  have hx30 : (30 : ℝ) ≤ x := by linarith
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hlog : 0 < log x := log_pos (by linarith)
  have hpoint : Chebyshev.theta x / log x ≤
      (27639 / 25000 : ℝ) * x / log x +
        (5000 / 1791 : ℝ) * log x := by
    apply (div_le_iff₀ hlog).2
    calc
      Chebyshev.theta x ≤ Chebyshev.psi x := Chebyshev.theta_le_psi x
      _ ≤ (27639 / 25000 : ℝ) * x +
          (5000 / 1791 : ℝ) * log x ^ 2 := psi_upper_sharp hx30
      _ = ((27639 / 25000 : ℝ) * x / log x +
          (5000 / 1791 : ℝ) * log x) * log x := by
        field_simp [ne_of_gt hlog]
  have hlate0 := integral_theta_30_upper hx30
  have hImaj := integral_inv_log_sq_majorized hx
  rw [invLogSquareMajorant] at hImaj
  have hlogDiv : log (x / 30) ≤ log x :=
    log_le_log (by positivity) (div_le_self hxpos.le (by norm_num))
  have hlate :
      (∫ t in (30 : ℝ)..x, Chebyshev.theta t / (t * log t ^ 2)) ≤
        (333 / 200 : ℝ) * x / log x ^ 2 + 5 * log x := by
    calc
      (∫ t in (30 : ℝ)..x, Chebyshev.theta t / (t * log t ^ 2)) ≤
          (111 / 100 : ℝ) * (∫ t in (30 : ℝ)..x, 1 / log t ^ 2) +
            5 * log (x / 30) := hlate0
      _ ≤ (111 / 100 : ℝ) * ((3 / 2 : ℝ) * x / log x ^ 2) +
          5 * log x := by nlinarith
      _ = (333 / 200 : ℝ) * x / log x ^ 2 + 5 * log x := by ring
  have hInt230 : IntervalIntegrable
      (fun t : ℝ => Chebyshev.theta t / (t * log t ^ 2))
      MeasureTheory.volume 2 30 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)]
    exact Chebyshev.integrableOn_theta_div_id_mul_log_sq 30
  have hInt30x : IntervalIntegrable
      (fun t : ℝ => Chebyshev.theta t / (t * log t ^ 2))
      MeasureTheory.volume 30 x := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx30]
    exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq x).mono_set (by
      intro t ht
      exact ⟨by linarith [ht.1], ht.2⟩)
  have hcount := Chebyshev.primeCounting_eq_theta_div_log_add_integral hx2
  rw [← intervalIntegral.integral_add_adjacent_intervals hInt230 hInt30x] at hcount
  nlinarith [integral_theta_2_30_le_ten]

lemma primeCounting_lower_large {x : ℝ} (hx : 30 ≤ x) :
    ((92129 / 100000 : ℝ) * x - 5 * log x + 5) / log x ≤
      (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  have hxpos : 0 < x := by linarith
  have hlog : 0 < log x := log_pos (by linarith)
  apply (div_le_iff₀ hlog).2
  have hpsi := ElementaryChebyshev.psi_lower x hx
  have ha := ElementaryChebyshev.a_bound.1
  have hcount := Chebyshev.psi_le_primeCounting_mul_log' x
  norm_num at ha
  nlinarith

lemma log_20000_lower : (99 / 10 : ℝ) < log 20000 := by
  rw [show (20000 : ℝ) = 2 ^ 5 * 5 ^ 4 by norm_num,
    log_mul (by norm_num) (by norm_num), log_pow, log_pow]
  norm_num
  nlinarith [Real.log_two_gt_d9, Real.log_five_gt_d9]

lemma log_20000_upper : log (20000 : ℝ) < 10 := by
  rw [show (20000 : ℝ) = 2 ^ 5 * 5 ^ 4 by norm_num,
    log_mul (by norm_num) (by norm_num), log_pow, log_pow]
  norm_num
  nlinarith [Real.log_two_lt_d9, Real.log_five_lt_d9]

lemma log_sq_div_large {x : ℝ} (hx : 20000 ≤ x) :
    log x ^ 2 / x ≤ (1 / 200 : ℝ) := by
  have hlogBaseLower : 2 ≤ log (20000 : ℝ) := by
    linarith [log_20000_lower]
  have hbase : exp 2 ≤ (20000 : ℝ) :=
    (le_log_iff_exp_le (by norm_num : (0 : ℝ) < 20000)).mp hlogBaseLower
  have hxmem : x ∈ Set.Ici (exp 2) := hbase.trans hx
  have hratio := ElementaryChebyshev.log_sq_div_antitone_on hbase hxmem hx
  have hbaseRatio : log (20000 : ℝ) ^ 2 / 20000 ≤ (1 / 200 : ℝ) := by
    have hsquare : log (20000 : ℝ) ^ 2 ≤ 100 := by
      nlinarith [log_20000_lower, log_20000_upper]
    calc
      log (20000 : ℝ) ^ 2 / 20000 ≤ 100 / 20000 := by gcongr
      _ = (1 / 200 : ℝ) := by norm_num
  exact hratio.trans hbaseRatio

lemma log_div_large {x : ℝ} (hx : 20000 ≤ x) :
    log x / x ≤ (1 / 2000 : ℝ) := by
  have hlogBaseLower : 1 ≤ log (20000 : ℝ) := by
    linarith [log_20000_lower]
  have hbase : exp 1 ≤ (20000 : ℝ) :=
    (le_log_iff_exp_le (by norm_num : (0 : ℝ) < 20000)).mp hlogBaseLower
  have hxmem : x ∈ Set.Ici (exp 1) := hbase.trans hx
  have hratio := Real.log_div_self_antitoneOn hbase hxmem hx
  have hbaseRatio : log (20000 : ℝ) / 20000 ≤ (1 / 2000 : ℝ) := by
    nlinarith [log_20000_upper]
  exact hratio.trans hbaseRatio

lemma analytic_three_primeCounting_le_five {x : ℝ} (hx : 20000 ≤ x) :
    3 * (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤
      (Nat.primeCounting ⌊5 * x⌋₊ : ℝ) := by
  have hx10000 : (10000 : ℝ) ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < log x := log_pos (by linarith)
  have hL : (99 / 10 : ℝ) ≤ log x := by
    have hmono : log (20000 : ℝ) ≤ log x := log_le_log (by norm_num) hx
    linarith [log_20000_lower]
  have hMpos : 0 < log (5 * x) := log_pos (by nlinarith)
  have hM : log (5 * x) ≤ (1151 / 990 : ℝ) * log x := by
    rw [log_mul (by norm_num : (5 : ℝ) ≠ 0) (ne_of_gt hxpos)]
    have hlog5 : log (5 : ℝ) ≤ (161 / 100 : ℝ) := by
      nlinarith [Real.log_five_lt_d9]
    nlinarith [mul_le_mul_of_nonneg_left hL (by norm_num : (0 : ℝ) ≤ 161 / 990)]
  have hInv : x / log x ^ 2 ≤ (10 / 99 : ℝ) * (x / log x) := by
    have hInvL : 1 / log x ≤ (10 / 99 : ℝ) := by
      apply (div_le_iff₀ hLpos).2
      nlinarith
    calc
      x / log x ^ 2 = (x / log x) * (1 / log x) := by
        field_simp [ne_of_gt hLpos]
      _ ≤ (x / log x) * (10 / 99 : ℝ) :=
        mul_le_mul_of_nonneg_left hInvL (div_nonneg hxpos.le hLpos.le)
      _ = (10 / 99 : ℝ) * (x / log x) := by ring
  have hLeading :
      ((92129 / 100000 : ℝ) * 5 * (990 / 1151 : ℝ)) * x / log x ≤
        (92129 / 100000 : ℝ) * (5 * x) / log (5 * x) := by
    apply (le_div_iff₀ hMpos).2
    calc
      (((92129 / 100000 : ℝ) * 5 * (990 / 1151 : ℝ)) * x / log x) *
          log (5 * x) ≤
        (((92129 / 100000 : ℝ) * 5 * (990 / 1151 : ℝ)) * x / log x) *
          ((1151 / 990 : ℝ) * log x) := by
            gcongr
      _ = (92129 / 100000 : ℝ) * (5 * x) := by
        field_simp [ne_of_gt hLpos]
  have hsq := log_sq_div_large hx
  have hlin := log_div_large hx
  have hsq' : log x ^ 2 ≤ (1 / 200 : ℝ) * x :=
    (div_le_iff₀ hxpos).mp hsq
  have hlin' : log x ≤ (1 / 2000 : ℝ) * x :=
    (div_le_iff₀ hxpos).mp hlin
  have htail :
      3 * (13955 / 1791 : ℝ) * log x + 35 ≤
        (((92129 / 100000 : ℝ) * 5 * (990 / 1151 : ℝ)) -
          3 * (27639 / 25000 : ℝ) -
          3 * (333 / 200 : ℝ) * (10 / 99 : ℝ)) * x / log x := by
    apply (le_div_iff₀ hLpos).2
    have hxnonneg : 0 ≤ x := hxpos.le
    calc
      (3 * (13955 / 1791 : ℝ) * log x + 35) * log x =
          3 * (13955 / 1791 : ℝ) * log x ^ 2 + 35 * log x := by ring
      _ ≤ (3 * (13955 / 1791 : ℝ) * (1 / 200 : ℝ) +
          35 * (1 / 2000 : ℝ)) * x := by
        nlinarith [mul_le_mul_of_nonneg_left hsq'
            (by norm_num : (0 : ℝ) ≤ 3 * (13955 / 1791 : ℝ)),
          mul_le_mul_of_nonneg_left hlin' (by norm_num : (0 : ℝ) ≤ 35)]
      _ ≤ (((92129 / 100000 : ℝ) * 5 * (990 / 1151 : ℝ)) -
          3 * (27639 / 25000 : ℝ) -
          3 * (333 / 200 : ℝ) * (10 / 99 : ℝ)) * x := by
        have : (3 * (13955 / 1791 : ℝ) * (1 / 200 : ℝ) +
            35 * (1 / 2000 : ℝ)) ≤
            ((92129 / 100000 : ℝ) * 5 * (990 / 1151 : ℝ)) -
              3 * (27639 / 25000 : ℝ) -
              3 * (333 / 200 : ℝ) * (10 / 99 : ℝ) := by norm_num
        exact mul_le_mul_of_nonneg_right this hxnonneg
  have hformula :
      3 * ((27639 / 25000 : ℝ) * x / log x +
        (333 / 200 : ℝ) * x / log x ^ 2 +
        (13955 / 1791 : ℝ) * log x + 10) ≤
      ((92129 / 100000 : ℝ) * 5 * (990 / 1151 : ℝ)) * x / log x - 5 := by
    have hInvScaled := mul_le_mul_of_nonneg_left hInv
      (by norm_num : (0 : ℝ) ≤ 3 * (333 / 200 : ℝ))
    ring_nf at hInvScaled htail ⊢
    linarith
  have hLowerAlgebra :
      (92129 / 100000 : ℝ) * (5 * x) / log (5 * x) - 5 ≤
        ((92129 / 100000 : ℝ) * (5 * x) - 5 * log (5 * x) + 5) /
          log (5 * x) := by
    have hfive : 0 ≤ (5 : ℝ) / log (5 * x) := div_nonneg (by norm_num) hMpos.le
    field_simp [ne_of_gt hMpos] at hfive ⊢
    linarith
  have hUpper := primeCounting_upper_large hx10000
  have hLower := primeCounting_lower_large (x := 5 * x) (by nlinarith)
  calc
    3 * (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤
        3 * ((27639 / 25000 : ℝ) * x / log x +
          (333 / 200 : ℝ) * x / log x ^ 2 +
          (13955 / 1791 : ℝ) * log x + 10) := by nlinarith
    _ ≤ ((92129 / 100000 : ℝ) * 5 * (990 / 1151 : ℝ)) * x / log x - 5 :=
      hformula
    _ ≤ (92129 / 100000 : ℝ) * (5 * x) / log (5 * x) - 5 := by
      linarith
    _ ≤ ((92129 / 100000 : ℝ) * (5 * x) - 5 * log (5 * x) + 5) /
        log (5 * x) := hLowerAlgebra
    _ ≤ (Nat.primeCounting ⌊5 * x⌋₊ : ℝ) := hLower

end Erdos534
