import ErdosProblems.Erdos49.BasicScaleBounds

/-!
# Primary and secondary main terms

The finite assembly theorem has three nonexceptional terms.  Here they are
converted to `N / log N` plus a fixed multiple of `taoErrorScale`.
-/

open Filter Set Topology

namespace Erdos49

noncomputable section

lemma scale_log2_add_one_upper {N : ℕ} (hs : ScaleFacts N) :
    ((N.log2 + 1 : ℕ) : ℝ) ≤ 3 * Real.log (N : ℝ) := by
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlog2pos : 0 < Real.log 2 := by linarith
  have hnat := Real.log2_le_logb N
  have hlogb : (N.log2 : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 := by
    simpa [Real.logb] using hnat
  have hdiv : Real.log (N : ℝ) / Real.log 2 ≤
      2 * Real.log (N : ℝ) := by
    apply (div_le_iff₀ hlog2pos).2
    have hh : 0 ≤ Real.log (N : ℝ) := by linarith [scale_h_ge hs]
    nlinarith
  push_cast
  nlinarith [scale_h_ge hs]

lemma secondaryTerm_le_errorScale {N : ℕ} (hs : ScaleFacts N) :
    8000 * (N : ℝ) * (1 + Real.log N) *
        (N.log2 + 1 : ℕ) ^ 2 / secondaryT (scaleH N) ≤
      144000 * taoErrorScale N := by
  let h := Real.log (N : ℝ)
  have hh : 0 < h := by dsimp only [h]; linarith [scale_h_ge hs]
  have hH : h ≤ (scaleH N : ℝ) := Nat.le_ceil h
  have hHpow : h ^ 6 ≤ (scaleH N : ℝ) ^ 6 :=
    pow_le_pow_left₀ hh.le hH 6
  have hden : h ^ 6 ≤ (secondaryT (scaleH N) : ℝ) := by
    simpa [secondaryT] using hHpow
  have hdenpos : (0 : ℝ) < secondaryT (scaleH N) := by
    exact (pow_pos hh 6).trans_le hden
  have hlogplus : 1 + h ≤ 2 * h := by
    linarith [scale_h_ge hs]
  have hlog2 := scale_log2_add_one_upper hs
  have hnum :
      8000 * (N : ℝ) * (1 + h) * ((N.log2 + 1 : ℕ) : ℝ) ^ 2 ≤
        144000 * (N : ℝ) * h ^ 3 := by
    calc
      8000 * (N : ℝ) * (1 + h) * ((N.log2 + 1 : ℕ) : ℝ) ^ 2 ≤
          8000 * (N : ℝ) * (2 * h) * (3 * h) ^ 2 := by gcongr
      _ = 144000 * (N : ℝ) * h ^ 3 := by ring
  calc
    8000 * (N : ℝ) * (1 + Real.log N) *
        (N.log2 + 1 : ℕ) ^ 2 / secondaryT (scaleH N) ≤
        (144000 * (N : ℝ) * h ^ 3) / (h ^ 6) := by
      exact div_le_div₀ (by positivity) (by simpa [h] using hnum)
        (pow_pos hh 6) hden
    _ = 144000 * (N : ℝ) / h ^ 3 := by field_simp
    _ ≤ 144000 * ((N : ℝ) * scaleT N ^ 5 / h ^ 2) := by
      have ht : (1 : ℝ) ≤ scaleT N ^ 5 := by
        have ht1 : (1 : ℝ) ≤ scaleT N := by linarith [hs.t_ge]
        simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) ht1 5
      have hcore : (N : ℝ) / h ^ 3 ≤
          (N : ℝ) * scaleT N ^ 5 / h ^ 2 := by
        apply (div_le_div_iff₀ (pow_pos hh 3) (pow_pos hh 2)).2
        have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        have hh1 : (1 : ℝ) ≤ h := by linarith [scale_h_ge hs]
        have hhpow : h ^ 2 ≤ scaleT N ^ 5 * h ^ 3 := by
          calc
            h ^ 2 = 1 * h ^ 2 := by ring
            _ ≤ scaleT N ^ 5 * h ^ 2 :=
              mul_le_mul_of_nonneg_right ht (sq_nonneg h)
            _ ≤ scaleT N ^ 5 * h ^ 3 := by
              apply mul_le_mul_of_nonneg_left
              · calc
                  h ^ 2 = h ^ 2 * 1 := by ring
                  _ ≤ h ^ 2 * h :=
                    mul_le_mul_of_nonneg_left hh1 (sq_nonneg h)
                  _ = h ^ 3 := by ring
              · exact zero_le_one.trans ht
        calc
          (N : ℝ) * h ^ 2 ≤ (N : ℝ) *
              (scaleT N ^ 5 * h ^ 3) :=
            mul_le_mul_of_nonneg_left hhpow hN0
          _ = (N : ℝ) * scaleT N ^ 5 * h ^ 3 := by ring
      calc
        144000 * (N : ℝ) / h ^ 3 =
            144000 * ((N : ℝ) / h ^ 3) := by ring
        _ ≤ 144000 * ((N : ℝ) * scaleT N ^ 5 / h ^ 2) :=
          mul_le_mul_of_nonneg_left hcore (by norm_num)
    _ = 144000 * taoErrorScale N := by unfold taoErrorScale; rfl

lemma primaryLeading_le {N : ℕ} (hs : ScaleFacts N) :
    (N : ℝ) / Real.log (scaleW N : ℝ) ≤
      (N : ℝ) / Real.log (N : ℝ) + 60 * taoErrorScale N := by
  let t := scaleT N
  let h := Real.log (N : ℝ)
  let B := 7 + 2 * t ^ 4 + 20 * t
  have ht : 0 < t := by dsimp only [t]; linarith [hs.t_ge]
  have hh : 0 < h := by dsimp only [h]; linarith [scale_h_ge hs]
  have hBhalf : B ≤ h / 2 := by
    have hp := scalePolynomialFacts_of_core (N := N) ⟨hs.t_ge, hs.core_bound⟩
    simpa [B, h, t] using hp.B_small
  have hsub : 0 < h - B := by linarith
  have hlogW : h - B ≤ Real.log (scaleW N : ℝ) := by
    simpa [h, B, t] using hs.logW_sharp
  have hB : B ≤ 30 * t ^ 5 := by
    dsimp only [B]
    have ht4 : t ^ 4 ≤ t ^ 5 := by
      calc
        t ^ 4 = t ^ 4 * 1 := by ring
        _ ≤ t ^ 4 * t := by gcongr; linarith [hs.t_ge]
        _ = t ^ 5 := by ring
    have htlin : t ≤ t ^ 5 := by
      calc
        t ≤ t ^ 2 := by nlinarith [hs.t_ge]
        _ ≤ t ^ 5 := pow_le_pow_right₀ (by linarith [hs.t_ge]) (by norm_num)
    have hone : (1 : ℝ) ≤ t ^ 5 := by nlinarith [hs.t_ge]
    nlinarith
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hinv : 1 / (h - B) ≤ 1 / h + 2 * B / h ^ 2 := by
    have hBid : 1 / (h - B) = 1 / h + B / (h * (h - B)) := by
      field_simp
      ring
    rw [hBid]
    have hhalfsub : h / 2 ≤ h - B := by linarith
    have hinvsub : 1 / (h - B) ≤ 2 / h := by
      calc
        1 / (h - B) ≤ 1 / (h / 2) :=
          one_div_le_one_div_of_le (by positivity) hhalfsub
        _ = 2 / h := by field_simp
    have hfrac : B / (h * (h - B)) ≤ 2 * B / h ^ 2 := by
      calc
        B / (h * (h - B)) = (B / h) * (1 / (h - B)) := by
          field_simp
        _ ≤ (B / h) * (2 / h) :=
          mul_le_mul_of_nonneg_left hinvsub (div_nonneg hB0 hh.le)
        _ = 2 * B / h ^ 2 := by ring
    simpa only [add_comm] using add_le_add_left hfrac (1 / h)
  calc
    (N : ℝ) / Real.log (scaleW N : ℝ) ≤ (N : ℝ) / (h - B) := by
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg N) hsub hlogW
    _ = (N : ℝ) * (1 / (h - B)) := by ring
    _ ≤ (N : ℝ) * (1 / h + 2 * B / h ^ 2) :=
      mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg N)
    _ = (N : ℝ) / h + 2 * (N : ℝ) * B / h ^ 2 := by ring
    _ ≤ (N : ℝ) / h + 2 * (N : ℝ) * (30 * t ^ 5) / h ^ 2 := by
      gcongr
    _ = (N : ℝ) / h + 60 * ((N : ℝ) * t ^ 5 / h ^ 2) := by ring
    _ = (N : ℝ) / Real.log (N : ℝ) + 60 * taoErrorScale N := by
      unfold taoErrorScale
      rfl

lemma primaryCorrection_le_errorScale {N : ℕ} {c C : ℝ}
    (hs : ScaleFacts N) (hc : 0 < c) (hC : 0 ≤ C)
    (hmedium : (2000 * C) * Real.exp
      (4 * scaleT N ^ 4 + 21 * scaleT N -
        c * Real.exp (scaleT N / 20)) ≤ 1)
    (hsqrtDecay : 6000 * Real.exp
      (4 * scaleT N ^ 4 + 23 * scaleT N -
        Real.exp (scaleT N) / 2) ≤ 1) :
    ((((N / scaleW N + 1) * scaleD N : ℕ) : ℝ) * scaleD N) *
        ((2 + 2 * thetaUniformError c C N) /
          Real.log (scaleW N : ℝ)) ≤
      2 * taoErrorScale N := by
  let t := scaleT N
  let h := Real.log (N : ℝ)
  let cell := ((((N / scaleW N + 1) * scaleD N : ℕ) : ℝ) * scaleD N)
  let M := C * (N : ℝ) * Real.exp
    (-c * Real.log (scaleW N - 1 : ℕ) ^ ((1 : ℝ) / 10))
  let S := 2 * Real.sqrt N * Real.log N
  have ht : 0 < t := by dsimp only [t]; linarith [hs.t_ge]
  have ht5 : (1 : ℝ) ≤ t ^ 5 := by
    have ht10 : (10 : ℝ) ≤ t := by simpa [t] using hs.t_ge
    have ht1 : (1 : ℝ) ≤ t := by linarith
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) ht1 5
  have hmedium' : (2000 * C) * Real.exp
      (4 * t ^ 4 + 21 * t - c * Real.exp (t / 20)) ≤ 1 := by
    simpa [t] using hmedium
  have hsqrtDecay' : 6000 * Real.exp
      (4 * t ^ 4 + 23 * t - Real.exp t / 2) ≤ 1 := by
    simpa [t] using hsqrtDecay
  have hh : 0 < h := by dsimp only [h]; linarith [scale_h_ge hs]
  have hh1 : (1 : ℝ) ≤ h := by linarith [scale_h_ge hs]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hs.N_pos
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast hs.N_pos
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt N := by
    have hsqrt0 := Real.sqrt_nonneg (N : ℝ)
    have hsquare := Real.sq_sqrt (Nat.cast_nonneg N)
    nlinarith
  have hunit : (1 : ℝ) ≤ Real.sqrt N * h :=
    by
      have hprod : 0 ≤ (Real.sqrt N - 1) * (h - 1) :=
        mul_nonneg (sub_nonneg.mpr hsqrtOne) (sub_nonneg.mpr hh1)
      nlinarith
  have hM0 : 0 ≤ M := by dsimp only [M]; positivity
  have hS0 : 0 ≤ S := by dsimp only [S]; positivity
  have hcell0 : 0 ≤ cell := by dsimp only [cell]; positivity
  have hcell := primary_cell_factor_bound hs
  have hnum : 2 + 2 * thetaUniformError c C N ≤ 2 * M + 3 * S := by
    unfold thetaUniformError
    dsimp only [M, S]
    nlinarith
  have hlogWpos : 0 < Real.log (scaleW N : ℝ) := by
    apply Real.log_pos
    have hW3 := hs.W_three
    have hWnat : 1 < scaleW N := by omega
    exact_mod_cast hWnat
  have hdiv : (2 + 2 * thetaUniformError c C N) /
      Real.log (scaleW N : ℝ) ≤ (2 * (2 * M + 3 * S)) / h := by
    calc
      (2 + 2 * thetaUniformError c C N) /
          Real.log (scaleW N : ℝ) ≤ (2 * M + 3 * S) / (h / 2) := by
        exact div_le_div₀ (by positivity) hnum (by positivity) (by
          simpa [h] using hs.logW_lower)
      _ = (2 * (2 * M + 3 * S)) / h := by field_simp
  have hsplit : cell * ((2 + 2 * thetaUniformError c C N) /
      Real.log (scaleW N : ℝ)) ≤
      4 * cell * M / h + 12 * cell * Real.sqrt N := by
    apply (mul_le_mul_of_nonneg_left hdiv hcell0).trans_eq
    dsimp only [S]
    field_simp
    ring
  have hpower := scale_medium_power_lower hs
  have hmediumExp : Real.exp
      (-c * Real.log (scaleW N - 1 : ℕ) ^ ((1 : ℝ) / 10)) ≤
      Real.exp (-c * Real.exp (t / 20)) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hpower hc.le
    dsimp only [t]
    nlinarith
  have hmediumTerm : 4 * cell * M / h ≤ taoErrorScale N := by
    calc
      4 * cell * M / h ≤ 4 *
          (500 * Real.exp (4 * t ^ 4 + 20 * t)) * M / h := by
        gcongr
      _ ≤
          2000 * C * (N : ℝ) *
            (Real.exp (4 * t ^ 4 + 20 * t) *
              Real.exp (-c * Real.exp (t / 20))) / h := by
        dsimp only [M]
        calc
          4 * (500 * Real.exp (4 * t ^ 4 + 20 * t)) *
                (C * (N : ℝ) *
                  Real.exp (-c * Real.log (scaleW N - 1 : ℕ) ^
                    ((1 : ℝ) / 10))) / h =
              (2000 * C * (N : ℝ) *
                Real.exp (4 * t ^ 4 + 20 * t) / h) *
                  Real.exp (-c * Real.log (scaleW N - 1 : ℕ) ^
                    ((1 : ℝ) / 10)) := by ring
          _ ≤ (2000 * C * (N : ℝ) *
                Real.exp (4 * t ^ 4 + 20 * t) / h) *
                  Real.exp (-c * Real.exp (t / 20)) :=
            mul_le_mul_of_nonneg_left hmediumExp (by positivity)
          _ = 2000 * C * (N : ℝ) *
              (Real.exp (4 * t ^ 4 + 20 * t) *
                Real.exp (-c * Real.exp (t / 20))) / h := by ring
      _ = ((N : ℝ) / h ^ 2) *
          ((2000 * C) * Real.exp
            (4 * t ^ 4 + 21 * t - c * Real.exp (t / 20))) := by
        have heh : Real.exp t = h := by
          simpa [t, h] using scale_exp_t hs
        rw [show Real.exp (4 * t ^ 4 + 20 * t) *
            Real.exp (-c * Real.exp (t / 20)) =
            Real.exp (4 * t ^ 4 + 20 * t -
              c * Real.exp (t / 20)) by
          rw [← Real.exp_add]
          congr 1 <;> ring]
        rw [show Real.exp (4 * t ^ 4 + 21 * t -
              c * Real.exp (t / 20)) =
            Real.exp (4 * t ^ 4 + 20 * t -
              c * Real.exp (t / 20)) * Real.exp t by
          rw [← Real.exp_add]
          congr 1 <;> ring, heh]
        field_simp
      _ ≤ (N : ℝ) / h ^ 2 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          hmedium' (by positivity : 0 ≤ (N : ℝ) / h ^ 2)
      _ ≤ (N : ℝ) * t ^ 5 / h ^ 2 := by
        have hbase : 0 ≤ (N : ℝ) / h ^ 2 := by positivity
        calc
          (N : ℝ) / h ^ 2 = ((N : ℝ) / h ^ 2) * 1 := by ring
          _ ≤ ((N : ℝ) / h ^ 2) * t ^ 5 :=
            mul_le_mul_of_nonneg_left ht5 hbase
          _ = (N : ℝ) * t ^ 5 / h ^ 2 := by ring
      _ = taoErrorScale N := by unfold taoErrorScale; rfl
  have hsqrtForm : Real.sqrt (N : ℝ) = Real.exp (h / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hNpos]
    congr 1
    dsimp only [h]
    ring
  have hNForm : (N : ℝ) = Real.exp h := by
    rw [Real.exp_log hNpos]
  have hhForm : h = Real.exp t := by
    simpa [h, t] using (scale_exp_t hs).symm
  have hsqrtTerm : 12 * cell * Real.sqrt N ≤ taoErrorScale N := by
    calc
      12 * cell * Real.sqrt N ≤
          6000 * Real.exp (4 * t ^ 4 + 20 * t) * Real.sqrt N := by
        calc
          12 * cell * Real.sqrt N ≤
              12 * (500 * Real.exp (4 * t ^ 4 + 20 * t)) *
                Real.sqrt N := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (by simpa [cell, t] using hcell)
                (by norm_num)) (Real.sqrt_nonneg N)
          _ = 6000 * Real.exp (4 * t ^ 4 + 20 * t) * Real.sqrt N := by ring
      _ = 6000 * Real.exp (4 * t ^ 4 + 20 * t + h / 2) := by
        rw [hsqrtForm]
        rw [show 6000 * Real.exp (4 * t ^ 4 + 20 * t) *
            Real.exp (h / 2) = 6000 *
              (Real.exp (4 * t ^ 4 + 20 * t) * Real.exp (h / 2)) by ring,
          ← Real.exp_add]
      _ ≤ 6000 * Real.exp
          (4 * t ^ 4 + 21 * t + h / 2) := by
        gcongr
        nlinarith
      _ ≤ t ^ 5 * (6000 * Real.exp
          (4 * t ^ 4 + 21 * t + h / 2)) := by
        nlinarith [Real.exp_pos (4 * t ^ 4 + 21 * t + h / 2)]
      _ = ((N : ℝ) * t ^ 5 / h ^ 2) *
          (6000 * Real.exp
            (4 * t ^ 4 + 23 * t - Real.exp t / 2)) := by
        rw [hNForm, hhForm]
        have hinv : (Real.exp t ^ 2)⁻¹ = Real.exp (-2 * t) := by
          rw [show -2 * t = -(t + t) by ring, Real.exp_neg, Real.exp_add]
          rw [pow_two]
        have hcombine : Real.exp (Real.exp t) * Real.exp (-2 * t) *
              Real.exp (4 * t ^ 4 + 23 * t - Real.exp t / 2) =
            Real.exp (4 * t ^ 4 + 21 * t + Real.exp t / 2) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        rw [show Real.exp (Real.exp t) * t ^ 5 / Real.exp t ^ 2 =
            Real.exp (Real.exp t) * t ^ 5 * (Real.exp t ^ 2)⁻¹ by ring,
          hinv]
        rw [show Real.exp (Real.exp t) * t ^ 5 * Real.exp (-2 * t) *
              (6000 * Real.exp
                (4 * t ^ 4 + 23 * t - Real.exp t / 2)) =
            t ^ 5 * 6000 *
              (Real.exp (Real.exp t) * Real.exp (-2 * t) *
                Real.exp (4 * t ^ 4 + 23 * t - Real.exp t / 2)) by ring,
          hcombine]
        ring
      _ ≤ (N : ℝ) * t ^ 5 / h ^ 2 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          hsqrtDecay'
          (by positivity : 0 ≤ (N : ℝ) * t ^ 5 / h ^ 2)
      _ = taoErrorScale N := by unfold taoErrorScale; rfl
  exact hsplit.trans (by linarith)

theorem eventually_assembled_main_bound :
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N → TotientMonotoneOn A →
      (A.card : ℝ) ≤ (N : ℝ) / Real.log (N : ℝ) +
        144062 * taoErrorScale N +
          (exceptionalSet N (scaleL N) (scaleD N) (scaleR N)).card := by
  obtain ⟨c, C, hc, hC, htheta⟩ := exists_eventually_uniform_theta
  have hmedium := eventually_medium_cell_decay (c := c) (C := 2000 * C)
    hc (by positivity)
  have hsqrt := eventually_sqrt_cell_decay 6000 (by norm_num)
  filter_upwards [eventually_scaleFacts, htheta,
    scale_log_tendsto.eventually hmedium,
    scale_log_tendsto.eventually hsqrt] with N hs hthetaN hmediumN hsqrtN
  intro A hAI hmono
  have hfinite := assembled_finite_bound
    (N := N) (L := scaleL N) (D := scaleD N) (R := scaleR N)
    (W := scaleW N) (H := scaleH N) (A := A)
    (Err := thetaUniformError c C N)
    hAI hmono hs.L_pos hs.separation.1 hs.separation.2.1
      hs.separation.2.2 hs.D_one hs.W_three hs.W_scale
      hthetaN.1 hthetaN.2 hs.H_two hs.secondary_scale
  have hlead := primaryLeading_le hs
  have hcorr := primaryCorrection_le_errorScale hs hc hC hmediumN hsqrtN
  have hsecondary := secondaryTerm_le_errorScale hs
  linarith

#print axioms eventually_assembled_main_bound

end

end Erdos49
