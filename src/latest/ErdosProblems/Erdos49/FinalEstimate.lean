import ErdosProblems.Erdos49.MainTermBounds

/-!
# Final additive and relative estimates

This file combines all six exceptional pieces, then converts the resulting
additive estimate to Tao's relative prime-counting form.
-/

open Filter Set Topology

namespace Erdos49

noncomputable section

def taoRelativeRate (N : ℕ) : ℝ :=
  Real.log (Real.log (N : ℝ)) ^ 5 / Real.log (N : ℝ)

theorem eventually_exceptionalSet_le_errorScale :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      ((exceptionalSet N (scaleL N) (scaleD N) (scaleR N)).card : ℝ) ≤
        C * taoErrorScale N := by
  obtain ⟨Cb, hCb, hbasic⟩ := eventually_basicExceptional_bounds
  obtain ⟨Cp, hCp, hpair⟩ := eventually_pairExceptional_le_errorScale
  let Ct := (1 + 2 * mertensReciprocalError) *
    ((43 + 2 * mertensReciprocalError) * 4000) ^ 2
  let C := Cb + Cp + Ct
  have hCt : 0 ≤ Ct := by
    dsimp only [Ct]
    positivity [mertensReciprocalError_nonneg]
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  filter_upwards [hbasic, hpair,
    eventually_tripleExceptional_le_errorScale] with N hb hp ht
  have hcardNat := exceptionalSet_card_le_sum N (scaleL N) (scaleD N) (scaleR N)
  have hcard :
      ((exceptionalSet N (scaleL N) (scaleD N) (scaleR N)).card : ℝ) ≤
        ((smallExceptional N (scaleL N)).card : ℝ) +
        (smoothExceptional N (scaleR N)).card +
        (squareExceptional N (scaleL N)).card +
        (smoothTailExceptional N (scaleL N) (scaleD N)).card +
        (pairExceptional N (scaleL N) (scaleD N) (scaleR N)).card +
        (tripleExceptional N (scaleL N) (scaleR N)).card := by
    exact_mod_cast hcardNat
  dsimp only [C, Ct]
  linarith

theorem exists_eventually_additive_resolution :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N → TotientMonotoneOn A →
        (A.card : ℝ) ≤ (N : ℝ) / Real.log (N : ℝ) +
          C * taoErrorScale N := by
  obtain ⟨Ce, hCe, he⟩ := eventually_exceptionalSet_le_errorScale
  refine ⟨144062 + Ce, by positivity, ?_⟩
  filter_upwards [eventually_assembled_main_bound, he] with N hmain heN
  intro A hAI hmono
  have := hmain A hAI hmono
  linarith

lemma theta_nat_le_primeCounting_mul_log (N : ℕ) :
    Chebyshev.theta (N : ℝ) ≤
      (Nat.primeCounting N : ℝ) * Real.log (N : ℝ) := by
  rw [Chebyshev.theta_eq_sum_primesLE_log]
  calc
    (∑ p ∈ Nat.primesLE N, Real.log (p : ℝ)) ≤
        ∑ _p ∈ Nat.primesLE N, Real.log (N : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpdata := Nat.mem_primesLE.mp hp
      exact Real.log_le_log (by exact_mod_cast hpdata.2.pos)
        (by exact_mod_cast hpdata.1)
    _ = (Nat.primeCounting N : ℝ) * Real.log (N : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul,
        Nat.primesLE_card_eq_primeCounting]

lemma prime_comparison_of_theta_error {N : ℕ} (hs : ScaleFacts N)
    (htheta : |Chebyshev.theta (N : ℝ) - N| ≤
      (N : ℝ) / Real.log (N : ℝ) ^ 2) :
    (N : ℝ) / Real.log (N : ℝ) ≤
        (Nat.primeCounting N : ℝ) + taoErrorScale N ∧
      taoErrorScale N ≤
        2 * taoRelativeRate N * (Nat.primeCounting N : ℝ) := by
  let t := scaleT N
  let h := Real.log (N : ℝ)
  have ht : 0 < t := by dsimp only [t]; linarith [hs.t_ge]
  have ht5 : (1 : ℝ) ≤ t ^ 5 := by
    have ht1 : (1 : ℝ) ≤ t := by linarith [hs.t_ge]
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) ht1 5
  have hh : 0 < h := by dsimp only [h]; linarith [scale_h_ge hs]
  have hh2 : (2 : ℝ) ≤ h ^ 2 := by
    nlinarith [scale_h_ge hs]
  have hthetaLower : (N : ℝ) - (N : ℝ) / h ^ 2 ≤
      Chebyshev.theta (N : ℝ) := by
    have := (abs_le.mp htheta).1
    dsimp only [h] at this ⊢
    linarith
  have hthetaUpper := theta_nat_le_primeCounting_mul_log N
  have hpiRaw : (N : ℝ) / h - (N : ℝ) / h ^ 3 ≤
      (Nat.primeCounting N : ℝ) := by
    apply (le_of_mul_le_mul_right _ hh)
    calc
      ((N : ℝ) / h - (N : ℝ) / h ^ 3) * h =
          (N : ℝ) - (N : ℝ) / h ^ 2 := by field_simp
      _ ≤ Chebyshev.theta (N : ℝ) := hthetaLower
      _ ≤ (Nat.primeCounting N : ℝ) * h := by
        simpa [h] using hthetaUpper
  have hsmall : (N : ℝ) / h ^ 3 ≤ taoErrorScale N := by
    unfold taoErrorScale
    dsimp only [t, h]
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    apply (div_le_div_iff₀ (pow_pos hh 3) (pow_pos hh 2)).2
    have hh1 : (1 : ℝ) ≤ h := by
      dsimp only [h]
      linarith [scale_h_ge hs]
    have hpow : h ^ 2 ≤ t ^ 5 * h ^ 3 := by
      calc
        h ^ 2 = 1 * h ^ 2 := by ring
        _ ≤ t ^ 5 * h ^ 2 := mul_le_mul_of_nonneg_right ht5 (sq_nonneg h)
        _ ≤ t ^ 5 * h ^ 3 := by
          gcongr
          nlinarith
    convert mul_le_mul_of_nonneg_left hpow hN0 using 1 <;> simp [t] <;> ring
  have hfirst : (N : ℝ) / h ≤
      (Nat.primeCounting N : ℝ) + taoErrorScale N := by
    linarith
  have hpiLower : (N : ℝ) / (2 * h) ≤
      (Nat.primeCounting N : ℝ) := by
    apply (le_trans _ hpiRaw)
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have haux : (N : ℝ) / h ^ 3 ≤ (N : ℝ) / (2 * h) := by
      exact div_le_div_of_nonneg_left hN0 (by positivity)
        (by nlinarith [hh2] : 2 * h ≤ h ^ 3)
    calc
      (N : ℝ) / (2 * h) = (N : ℝ) / h - (N : ℝ) / (2 * h) := by
        field_simp
        ring
      _ ≤ (N : ℝ) / h - (N : ℝ) / h ^ 3 :=
        sub_le_sub_left haux _
  have hrate0 : 0 ≤ taoRelativeRate N := by
    unfold taoRelativeRate
    positivity
  have hsecond : taoErrorScale N ≤
      2 * taoRelativeRate N * (Nat.primeCounting N : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hpiLower
      (show 0 ≤ 2 * taoRelativeRate N by positivity)
    calc
      taoErrorScale N =
          2 * taoRelativeRate N * ((N : ℝ) / (2 * h)) := by
        unfold taoErrorScale taoRelativeRate scaleT
        dsimp only [h]
        field_simp
      _ ≤ 2 * taoRelativeRate N * (Nat.primeCounting N : ℝ) := hm
  exact ⟨by simpa [h] using hfirst, hsecond⟩

theorem eventually_prime_comparison :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) / Real.log (N : ℝ) ≤
          (Nat.primeCounting N : ℝ) + taoErrorScale N ∧
        taoErrorScale N ≤
          2 * taoRelativeRate N * (Nat.primeCounting N : ℝ) ∧
        0 ≤ taoRelativeRate N := by
  have hthetaReal := Analytic.eventually_mediumTheta_error_div_log_pow 2
    (by norm_num : (0 : ℝ) < 1)
  have hnat : Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  filter_upwards [eventually_scaleFacts, hnat.eventually hthetaReal] with N hs ht
  have ht' : |Chebyshev.theta (N : ℝ) - N| ≤
      (N : ℝ) / Real.log (N : ℝ) ^ 2 := by simpa using ht
  have hp := prime_comparison_of_theta_error hs ht'
  exact ⟨hp.1, hp.2, by
    unfold taoRelativeRate
    have ht0 : 0 ≤ Real.log (Real.log (N : ℝ)) := by
      have := hs.t_ge
      unfold scaleT at this
      linarith
    positivity⟩

theorem exists_eventually_relative_resolution :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N → TotientMonotoneOn A →
        (A.card : ℝ) ≤
          (1 + C * taoRelativeRate N) * (Nat.primeCounting N : ℝ) := by
  obtain ⟨Ca, hCa, hadd⟩ := exists_eventually_additive_resolution
  refine ⟨2 * (Ca + 1), by positivity, ?_⟩
  filter_upwards [hadd, eventually_prime_comparison] with N hA hprime
  intro A hAI hmono
  have hbound := hA A hAI hmono
  have hrate0 : 0 ≤ taoRelativeRate N := hprime.2.2
  calc
    (A.card : ℝ) ≤ (N : ℝ) / Real.log (N : ℝ) +
        Ca * taoErrorScale N := hbound
    _ ≤ (Nat.primeCounting N : ℝ) +
        (Ca + 1) * taoErrorScale N := by
      nlinarith [hprime.1]
    _ ≤ (Nat.primeCounting N : ℝ) +
        (Ca + 1) *
          (2 * taoRelativeRate N * (Nat.primeCounting N : ℝ)) := by
      have hmul : (Ca + 1) * taoErrorScale N ≤
          (Ca + 1) *
            (2 * taoRelativeRate N * (Nat.primeCounting N : ℝ)) :=
        mul_le_mul_of_nonneg_left hprime.2.1 (by linarith)
      exact add_le_add le_rfl hmul
    _ = (1 + (2 * (Ca + 1)) * taoRelativeRate N) *
        (Nat.primeCounting N : ℝ) := by ring

lemma taoRelativeRate_pos {N : ℕ} (hN : 10 ≤ N) :
    0 < taoRelativeRate N := by
  have hNreal : (10 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by norm_num) hNreal
  have hlog : 1 < Real.log (N : ℝ) := by
    exact (Real.lt_log_iff_exp_lt hNpos).2
      (lt_of_lt_of_le (lt_trans Real.exp_one_lt_three (by norm_num)) hNreal)
  unfold taoRelativeRate
  have hloglog : 0 < Real.log (Real.log (N : ℝ)) := Real.log_pos hlog
  exact div_pos (pow_pos hloglog 5) (lt_trans (by norm_num) hlog)

lemma primeCounting_pos_of_ten_le {N : ℕ} (hN : 10 ≤ N) :
    1 ≤ Nat.primeCounting N := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  apply Finset.one_le_card.mpr
  exact ⟨2, Nat.mem_primesLE.mpr ⟨by omega, Nat.prime_two⟩⟩

/-- The eventual relative estimate implies one uniform estimate for every
`N ≥ 10`: a finite sum absorbs the bounded initial interval. -/
theorem exists_uniform_relative_resolution :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 10 ≤ N →
      ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N → TotientMonotoneOn A →
        (A.card : ℝ) ≤
          (1 + C * taoRelativeRate N) * (Nat.primeCounting N : ℝ) := by
  obtain ⟨Ce, hCe, heventual⟩ := exists_eventually_relative_resolution
  rw [eventually_atTop] at heventual
  obtain ⟨X, hX⟩ := heventual
  let Cf : ℝ := ∑ n ∈ Finset.Icc 10 X, (n : ℝ) / taoRelativeRate n
  let C := Ce + Cf
  have hCf : 0 ≤ Cf := by
    dsimp only [Cf]
    apply Finset.sum_nonneg
    intro n hn
    have hn10 : 10 ≤ n := (Finset.mem_Icc.mp hn).1
    exact (div_nonneg (Nat.cast_nonneg n) (taoRelativeRate_pos hn10).le)
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact add_nonneg hCe hCf
  have hCeC : Ce ≤ C := by
    dsimp only [C]
    exact le_add_of_nonneg_right hCf
  have hCfC : Cf ≤ C := by
    dsimp only [C]
    exact le_add_of_nonneg_left hCe
  refine ⟨C, hC, ?_⟩
  intro N hN A hAI hmono
  have hrate : 0 < taoRelativeRate N := taoRelativeRate_pos hN
  by_cases hlarge : X ≤ N
  · have hCeBound := hX N hlarge A hAI hmono
    calc
      (A.card : ℝ) ≤
          (1 + Ce * taoRelativeRate N) * (Nat.primeCounting N : ℝ) := hCeBound
      _ ≤ (1 + C * taoRelativeRate N) * (Nat.primeCounting N : ℝ) := by
        have hpi : (0 : ℝ) ≤ Nat.primeCounting N := by positivity
        apply mul_le_mul_of_nonneg_right _ hpi
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hCeC hrate.le)
  · have hNX : N ≤ X := Nat.le_of_lt (Nat.lt_of_not_ge hlarge)
    have hmem : N ∈ Finset.Icc 10 X := Finset.mem_Icc.mpr ⟨hN, hNX⟩
    have hterm : (N : ℝ) / taoRelativeRate N ≤ Cf := by
      dsimp only [Cf]
      exact Finset.single_le_sum
        (fun n hn ↦ div_nonneg (Nat.cast_nonneg n)
          (taoRelativeRate_pos (Finset.mem_Icc.mp hn).1).le)
        hmem
    have hNleCf : (N : ℝ) ≤ Cf * taoRelativeRate N := by
      exact (div_le_iff₀ hrate).mp hterm
    have hcard : (A.card : ℝ) ≤ N := by
      have hcardNat : A.card ≤ N := by
        calc
          A.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hAI
          _ = N := by simp
      exact_mod_cast hcardNat
    have hpi : (1 : ℝ) ≤ Nat.primeCounting N := by
      exact_mod_cast primeCounting_pos_of_ten_le hN
    have hfactor : 0 ≤ 1 + C * taoRelativeRate N := by
      exact add_nonneg zero_le_one (mul_nonneg hC hrate.le)
    calc
      (A.card : ℝ) ≤ N := hcard
      _ ≤ Cf * taoRelativeRate N := hNleCf
      _ ≤ 1 + C * taoRelativeRate N := by
        exact (mul_le_mul_of_nonneg_right hCfC hrate.le).trans
          (le_add_of_nonneg_left zero_le_one)
      _ ≤ (1 + C * taoRelativeRate N) *
          (Nat.primeCounting N : ℝ) := by
        calc
          1 + C * taoRelativeRate N =
              (1 + C * taoRelativeRate N) * 1 := by ring
          _ ≤ (1 + C * taoRelativeRate N) *
              (Nat.primeCounting N : ℝ) :=
            mul_le_mul_of_nonneg_left hpi hfactor

#print axioms exists_eventually_relative_resolution
#print axioms exists_uniform_relative_resolution

end

end Erdos49
