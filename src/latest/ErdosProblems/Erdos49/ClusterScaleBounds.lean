import ErdosProblems.Erdos49.Decay

/-!
# Cluster estimates at Tao's scales

This file converts the two prime-cluster counting lemmas into multiples of
`taoErrorScale`.  The elementary logarithmic estimates are stated separately
so that the final assembly contains no hidden asymptotic bookkeeping.
-/

open Filter Set Topology
open scoped BigOperators

namespace Erdos49

noncomputable section

lemma log_sub_one_lower_of_three {Y : ℕ} (hY : 3 ≤ Y) {z : ℝ}
    (hz : z ≤ Real.log (Y : ℝ)) :
    z / 2 ≤ Real.log ((Y - 1 : ℕ) : ℝ) := by
  have hYm : (0 : ℝ) < (Y - 1 : ℕ) := by exact_mod_cast (by omega : 0 < Y - 1)
  have hlogTwo : Real.log 2 ≤ Real.log ((Y - 1 : ℕ) : ℝ) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast (show 2 ≤ Y - 1 by omega)
  by_cases hzTwo : z / 2 ≤ Real.log 2
  · exact hzTwo.trans hlogTwo
  have hquot : (Y : ℝ) / 2 ≤ (Y - 1 : ℕ) := by
    have hnat : Y ≤ 2 * (Y - 1) := by omega
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    exact_mod_cast (by simpa [mul_comm] using hnat)
  have hdiff : Real.log (Y : ℝ) - Real.log 2 ≤
      Real.log ((Y - 1 : ℕ) : ℝ) := by
    rw [← Real.log_div (by positivity) (by norm_num)]
    exact Real.log_le_log (by positivity) hquot
  linarith

lemma scale_pair_log_sub_one_lower {N : ℕ} (hs : ScaleFacts N) :
    Real.log (N : ℝ) / (4000 * scaleT N) ≤
      Real.log ((scalePairY N - 1 : ℕ) : ℝ) := by
  have h := log_sub_one_lower_of_three hs.pairY_three hs.pair_log_lower
  convert h using 1 <;> ring

lemma scale_triple_log_sub_one_lower {N : ℕ} (hs : ScaleFacts N) :
    Real.log (N : ℝ) / (4000 * scaleT N) ≤
      Real.log ((scaleTripleY N - 1 : ℕ) : ℝ) := by
  have h := log_sub_one_lower_of_three hs.tripleY_three hs.triple_log_lower
  convert h using 1 <;> ring

lemma scale_log_two_L_upper {N : ℕ} (hs : ScaleFacts N) :
    Real.log ((2 * scaleL N : ℕ) : ℝ) ≤ 22 * scaleT N := by
  have hL0 : (scaleL N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs.L_pos)
  rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) hL0]
  have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at hlog2
  have hlogL := scale_logL_upper hs
  norm_num only [Nat.cast_ofNat]
  nlinarith [hs.t_ge]

lemma scale_log_two_L_sq_upper {N : ℕ} (hs : ScaleFacts N) :
    Real.log ((2 * scaleL N ^ 2 : ℕ) : ℝ) ≤ 43 * scaleT N := by
  have hL0 : (scaleL N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs.L_pos)
  rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow,
    Real.log_mul (by norm_num) (pow_ne_zero 2 hL0), Real.log_pow]
  have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at hlog2
  have hlogL := scale_logL_upper hs
  norm_num only [Nat.cast_ofNat]
  nlinarith [hs.t_ge]

lemma scaleTripleY_le_scalePairY {N : ℕ} (hs : ScaleFacts N) :
    scaleTripleY N ≤ scalePairY N := by
  unfold scaleTripleY scalePairY
  have hLL : scaleL N ≤ scaleL N ^ 2 := by
    nlinarith [hs.L_pos]
  exact Nat.div_le_div_left hLL hs.L_pos

lemma eventually_scale_cutoffs_ge (X : ℕ) (hX : 0 < X) :
    ∀ᶠ N : ℕ in atTop,
      X ≤ scaleTripleY N ∧ X ≤ scalePairY N := by
  have ht : ∀ᶠ N : ℕ in atTop,
      Real.log (X : ℝ) ≤ 40 * scaleT N + 3 :=
    scale_log_tendsto.eventually_ge_atTop ((Real.log (X : ℝ) - 3) / 40)
      |>.mono (by
        intro N hN
        linarith)
  filter_upwards [eventually_scaleFacts, ht] with N hs htN
  have hcast : (X : ℝ) ≤ (scaleTripleY N : ℝ) := by
    calc
      (X : ℝ) = Real.exp (Real.log (X : ℝ)) := by
        rw [Real.exp_log]
        exact_mod_cast hX
      _ ≤ Real.exp (40 * scaleT N + 3) := Real.exp_le_exp.mpr htN
      _ ≤ Real.exp (Real.log (N : ℝ) / (2000 * scaleT N)) := by
        apply Real.exp_le_exp.mpr
        have hcore : 40 * scaleT N + 3 ≤
            Real.log (N : ℝ) / (2000 * scaleT N) := by
          have htpos : 0 < scaleT N :=
            (by norm_num : (0 : ℝ) < 10).trans_le hs.t_ge
          have ht6 : scaleT N ^ 2 ≤ (1 + scaleT N) ^ 6 := by
            have h1 : scaleT N ≤ 1 + scaleT N := by linarith
            have h2 := pow_le_pow_left₀ (by positivity) h1 2
            have h3 : (1 + scaleT N) ^ 2 ≤ (1 + scaleT N) ^ 6 :=
              pow_le_pow_right₀ (by linarith) (by norm_num)
            exact h2.trans h3
          have ht1 : scaleT N ≤ (1 + scaleT N) ^ 6 := by
            calc
              scaleT N ≤ 1 + scaleT N := by linarith
              _ = (1 + scaleT N) ^ (1 : ℕ) := (pow_one _).symm
              _ ≤ (1 + scaleT N) ^ (6 : ℕ) :=
                pow_le_pow_right₀ (by linarith) (by norm_num)
          apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2000 * scaleT N)).2
          nlinarith [hs.core_bound, ht6, ht1]
        exact hcore
      _ ≤ (scaleTripleY N : ℝ) := hs.tripleY_cast_lower
  have hnat : X ≤ scaleTripleY N := by exact_mod_cast hcast
  exact ⟨hnat, hnat.trans (scaleTripleY_le_scalePairY hs)⟩

lemma scale_L_gt_exp_one {N : ℕ} (hs : ScaleFacts N) :
    Real.exp 1 < (scaleL N : ℝ) := by
  calc
    Real.exp 1 < Real.exp (20 * scaleT N) :=
      Real.exp_lt_exp.mpr (by linarith [hs.t_ge])
    _ ≤ (scaleL N : ℝ) := hs.L_bounds.1

lemma scale_primeReciprocalInterval_upper {N Y : ℕ}
    (hs : ScaleFacts N) (hY : 3 ≤ Y) :
    primeReciprocalInterval (Y + 1) N ≤
      (1 + 2 * mertensReciprocalError) * scaleT N := by
  have hM := mertensReciprocalError_nonneg
  have ht0 : 0 ≤ scaleT N := by linarith [hs.t_ge]
  by_cases hYN : Y + 1 ≤ N
  · have hu := primeReciprocalInterval_upper (u := Y + 1) (v := N)
      (by omega) hYN
    have hYpos : (0 : ℝ) < Y := by exact_mod_cast (by omega : 0 < Y)
    have hlogYone : 1 < Real.log (Y : ℝ) := by
      rw [Real.lt_log_iff_exp_lt hYpos]
      exact Real.exp_one_lt_three.trans_le (by exact_mod_cast hY)
    have hloglogY : 0 ≤ Real.log (Real.log (Y : ℝ)) :=
      Real.log_nonneg hlogYone.le
    have herr : 2 * mertensReciprocalError / Real.log (Y : ℝ) ≤
        2 * mertensReciprocalError := by
      apply (div_le_iff₀ (by linarith : 0 < Real.log (Y : ℝ))).2
      nlinarith
    calc
      primeReciprocalInterval (Y + 1) N ≤
          Real.log (Real.log (N : ℝ)) -
            Real.log (Real.log (Y : ℝ)) +
              2 * mertensReciprocalError / Real.log (Y : ℝ) := by
        simpa using hu
      _ ≤ scaleT N + 2 * mertensReciprocalError := by
        unfold scaleT
        linarith
      _ ≤ (1 + 2 * mertensReciprocalError) * scaleT N := by
        nlinarith [hs.t_ge]
  · have hempty : Analytic.primeInterval (Y + 1) N = ∅ := by
      unfold Analytic.primeInterval
      ext p
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty,
        iff_false]
      intro hp
      exact hYN (hp.1.1.trans hp.1.2)
    simp [primeReciprocalInterval, hempty]
    positivity

lemma scale_pairCoefficient_upper {N : ℕ} (hs : ScaleFacts N) :
    pairCoefficient (scaleL N) (scalePairY N) ≤
      (100 + 8 * mertensReciprocalError) * 16000000 *
        scaleT N ^ 3 / Real.log (N : ℝ) ^ 2 := by
  let t := scaleT N
  let h := Real.log (N : ℝ)
  let K := 100 + 8 * mertensReciprocalError
  let z := h / (4000 * t)
  have ht : 0 < t := by dsimp only [t]; linarith [hs.t_ge]
  have hh : 0 < h := by dsimp only [h]; linarith [scale_h_ge hs]
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity [mertensReciprocalError_nonneg]
  have hz : 0 < z := by dsimp only [z]; positivity
  have hden : z ≤ Real.log ((scalePairY N - 1 : ℕ) : ℝ) := by
    simpa [z, h, t] using scale_pair_log_sub_one_lower hs
  have hdenpos : 0 < Real.log ((scalePairY N - 1 : ℕ) : ℝ) := hz.trans_le hden
  have hnum :
      16 + 4 * (Real.log ((2 * scaleL N : ℕ) : ℝ) +
        2 * mertensReciprocalError) ≤ K * t := by
    have hlog := scale_log_two_L_upper hs
    dsimp only [K, t]
    nlinarith [hs.t_ge, mertensReciprocalError_nonneg]
  unfold pairCoefficient
  apply (div_le_iff₀ (sq_pos_of_pos hdenpos)).2
  calc
    16 + 4 * (Real.log ((2 * scaleL N : ℕ) : ℝ) +
        2 * mertensReciprocalError) ≤ K * t := hnum
    _ = (K * 16000000 * t ^ 3 / h ^ 2) * z ^ 2 := by
      dsimp only [z]
      field_simp
      ring
    _ ≤ (K * 16000000 * t ^ 3 / h ^ 2) *
        Real.log ((scalePairY N - 1 : ℕ) : ℝ) ^ 2 := by
      apply mul_le_mul_of_nonneg_left
      · exact pow_le_pow_left₀ hz.le hden 2
      · positivity

lemma scale_tripleInnerBound_upper {N : ℕ} (hs : ScaleFacts N) :
    tripleInnerBound (scaleL N) (scaleTripleY N) ≤
      (43 + 2 * mertensReciprocalError) * 4000 *
        scaleT N ^ 2 / Real.log (N : ℝ) := by
  let t := scaleT N
  let h := Real.log (N : ℝ)
  let K := 43 + 2 * mertensReciprocalError
  let z := h / (4000 * t)
  have ht : 0 < t := by dsimp only [t]; linarith [hs.t_ge]
  have hh : 0 < h := by dsimp only [h]; linarith [scale_h_ge hs]
  have hz : 0 < z := by dsimp only [z]; positivity
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity [mertensReciprocalError_nonneg]
  have hden : z ≤ Real.log ((scaleTripleY N - 1 : ℕ) : ℝ) := by
    simpa [z, h, t] using scale_triple_log_sub_one_lower hs
  have hnum : Real.log ((2 * scaleL N ^ 2 : ℕ) : ℝ) +
      2 * mertensReciprocalError ≤ K * t := by
    have hlog := scale_log_two_L_sq_upper hs
    dsimp only [K, t]
    nlinarith [hs.t_ge, mertensReciprocalError_nonneg]
  unfold tripleInnerBound
  calc
    (Real.log ((2 * scaleL N ^ 2 : ℕ) : ℝ) +
        2 * mertensReciprocalError) /
          Real.log ((scaleTripleY N - 1 : ℕ) : ℝ) ≤
        (K * t) / z := by
      exact div_le_div₀ (mul_nonneg hK ht.le) hnum hz hden
    _ = K * 4000 * t ^ 2 / h := by
      dsimp only [z]
      field_simp

theorem eventually_pairExceptional_le_errorScale :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      ((pairExceptional N (scaleL N) (scaleD N) (scaleR N)).card : ℝ) ≤
        C * taoErrorScale N := by
  obtain ⟨Cs, hCs, hsmooth⟩ := exists_smooth_reciprocal_log_sq_bound
  obtain ⟨X, hXtwo, hprime⟩ := exists_primeCounting_nat_upper
  let K := Cs * 441 *
    ((100 + 8 * mertensReciprocalError) * 16000000)
  refine ⟨K, by dsimp only [K]; positivity [mertensReciprocalError_nonneg], ?_⟩
  filter_upwards [eventually_scaleFacts,
    eventually_scale_cutoffs_ge X (by omega)] with N hs hcut
  have hsum := hsmooth (scaleD N) (scaleL N) (scale_L_gt_exp_one hs)
  have hLoneNat : 1 ≤ scaleL N := hs.L_pos
  have hlognonneg : 0 ≤ Real.log (scaleL N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hLoneNat)
  have ht0 : 0 ≤ scaleT N := by linarith [hs.t_ge]
  have hsum' : (∑ d ∈ smoothUpTo (scaleD N) (scaleL N), (1 : ℝ) / d) ≤
      Cs * 441 * scaleT N ^ 2 := by
    calc
      (∑ d ∈ smoothUpTo (scaleD N) (scaleL N), (1 : ℝ) / d) ≤
          Cs * Real.log (scaleL N : ℝ) ^ 2 := hsum
      _ ≤ Cs * (21 * scaleT N) ^ 2 := by
        gcongr
        exact scale_logL_upper hs
      _ = Cs * 441 * scaleT N ^ 2 := by ring
  have hpair := pairExceptional_card_real_le
    (N := N) (L := scaleL N) (D := scaleD N) (R := scaleR N)
    (X₀ := X) (Y := scalePairY N) hs.L_pos rfl hs.pairY_three hcut.2 hprime
  have hcoeff := scale_pairCoefficient_upper hs
  have hcoeff0 : 0 ≤ pairCoefficient (scaleL N) (scalePairY N) := by
    unfold pairCoefficient
    positivity [mertensReciprocalError_nonneg]
  calc
    ((pairExceptional N (scaleL N) (scaleD N) (scaleR N)).card : ℝ) ≤
        (N : ℝ) *
          (∑ d ∈ smoothUpTo (scaleD N) (scaleL N), (1 : ℝ) / d) *
            pairCoefficient (scaleL N) (scalePairY N) := hpair
    _ ≤ (N : ℝ) * (Cs * 441 * scaleT N ^ 2) *
        (((100 + 8 * mertensReciprocalError) * 16000000) *
          scaleT N ^ 3 / Real.log (N : ℝ) ^ 2) := by
      gcongr
    _ = K * taoErrorScale N := by
      unfold taoErrorScale
      dsimp only [K]
      ring

theorem tripleExceptional_le_errorScale {N : ℕ} (hs : ScaleFacts N) :
    ((tripleExceptional N (scaleL N) (scaleR N)).card : ℝ) ≤
      ((1 + 2 * mertensReciprocalError) *
        ((43 + 2 * mertensReciprocalError) * 4000) ^ 2) *
          taoErrorScale N := by
  have htriple := tripleExceptional_card_real_le
    (N := N) (L := scaleL N) (R := scaleR N) (Y := scaleTripleY N)
    hs.L_pos rfl hs.tripleY_three
  have houter := scale_primeReciprocalInterval_upper hs hs.tripleY_three
  have hinner := scale_tripleInnerBound_upper hs
  have hinner0 : 0 ≤ tripleInnerBound (scaleL N) (scaleTripleY N) := by
    unfold tripleInnerBound
    positivity [mertensReciprocalError_nonneg]
  have houterRhs0 :
      0 ≤ (N : ℝ) * ((1 + 2 * mertensReciprocalError) * scaleT N) := by
    exact mul_nonneg (Nat.cast_nonneg N)
      (mul_nonneg (by linarith [mertensReciprocalError_nonneg])
        (by linarith [hs.t_ge]))
  calc
    ((tripleExceptional N (scaleL N) (scaleR N)).card : ℝ) ≤
        (N : ℝ) * primeReciprocalInterval (scaleTripleY N + 1) N *
          tripleInnerBound (scaleL N) (scaleTripleY N) ^ 2 := htriple
    _ ≤ (N : ℝ) *
        ((1 + 2 * mertensReciprocalError) * scaleT N) *
        (((43 + 2 * mertensReciprocalError) * 4000 *
          scaleT N ^ 2 / Real.log (N : ℝ)) ^ 2) := by
      gcongr
    _ = ((1 + 2 * mertensReciprocalError) *
        ((43 + 2 * mertensReciprocalError) * 4000) ^ 2) *
          taoErrorScale N := by
      unfold taoErrorScale
      ring

theorem eventually_tripleExceptional_le_errorScale :
    ∀ᶠ N : ℕ in atTop,
      ((tripleExceptional N (scaleL N) (scaleR N)).card : ℝ) ≤
        ((1 + 2 * mertensReciprocalError) *
          ((43 + 2 * mertensReciprocalError) * 4000) ^ 2) *
            taoErrorScale N :=
  eventually_scaleFacts.mono fun _ hs ↦ tripleExceptional_le_errorScale hs

#print axioms eventually_pairExceptional_le_errorScale
#print axioms eventually_tripleExceptional_le_errorScale

end

end Erdos49
