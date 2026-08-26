import ErdosProblems.Erdos327.Analytic.MixedScheduledSummation
import ErdosProblems.Erdos327.Analytic.PowerTail

/-!
# Moving-start summation of the mixed bulk main term

The certified mixed exponent is only slightly below `-1`, so a fixed
late tail is not enough: the lower endpoint must move with the roughness
cutoff.  Nonzero mixed bulk blocks satisfy `L ≤ 16 * 2^j`; this file
turns that support condition into the missing power of `log L`.
-/

namespace Erdos327.Analytic

open Filter Finset Real

open scoped BigOperators

noncomputable section

/-- A small rational power which absorbs the four scheduled logarithms
without exhausting either certified numerical margin. -/
def mixedBulkLogAbsorption : ℝ := 1 / 10000

theorem mixedBulkLogAbsorption_pos :
    0 < mixedBulkLogAbsorption := by
  norm_num [mixedBulkLogAbsorption]

/-- The absorbed bulk profile is still summable. -/
theorem mixedCanonicalCross_add_absorption_lt_neg_one :
    mixedCanonicalCrossExponent + mixedBulkLogAbsorption < -1 := by
  unfold mixedCanonicalCrossExponent mixedBulkLogAbsorption
    sourceAnatomySlope oddAnatomySlope
    mixedSourceWeightBase mixedOddWeightBase
  norm_num at ⊢
  nlinarith [Erdos327.log_qb_upper, Erdos327.log_qo_upper]

/-- The moving odd intercept still leaves more than one full negative
power of `log L` after the logarithmic absorption. -/
theorem mixedOddBudget_add_absorption_lt_one :
    oddBudgetSlope * log mixedOddWeightBase +
        mixedBulkLogAbsorption < 1 := by
  unfold oddBudgetSlope mixedOddWeightBase mixedBulkLogAbsorption
  norm_num at ⊢
  nlinarith [Erdos327.log_qo_upper]

/-- Natural dyadic lower endpoint forced by `L ≤ 16 * 2^j`. -/
def mixedBulkMovingStart (L : ℕ) : ℕ := Nat.log 2 L - 4

theorem mixedBulkMovingStart_le_of_near
    {L j : ℕ} (hnear : L ≤ 16 * dyadicScale j) :
    mixedBulkMovingStart L ≤ j := by
  have hlog :=
    Nat.log_mono_right (b := 2) hnear
  have hpow :
      16 * dyadicScale j = 2 ^ (j + 4) := by
    simp [dyadicScale, pow_add, mul_comm]
  rw [hpow, Nat.log_pow (by norm_num : 1 < 2)] at hlog
  unfold mixedBulkMovingStart
  omega

/-- The moving lower endpoint eventually dominates every fixed schedule
threshold. -/
theorem eventually_fixed_le_mixedBulkMovingStart (H : ℕ) :
    ∀ᶠ L : ℕ in atTop, H ≤ mixedBulkMovingStart L := by
  filter_upwards [eventually_ge_atTop (2 ^ (H + 4))] with L hL
  have hlog :
      H + 4 ≤ Nat.log 2 L := by
    simpa [Nat.log_pow (by norm_num : 1 < 2)] using
      (Nat.log_mono_right (b := 2) hL)
  unfold mixedBulkMovingStart
  omega

/-- Once the binary logarithm is at least nine, the moving natural
endpoint is bounded below by a fixed multiple of the real logarithm. -/
theorem log_div_le_mixedBulkMovingStart
    {L : ℕ} (hL : 3 ≤ L)
    (hnine : 9 ≤ Nat.log 2 L) :
    log (L : ℝ) / (2 * log 2) ≤
      (mixedBulkMovingStart L : ℝ) := by
  let n : ℕ := Nat.log 2 L
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hpowNat :
      L < 2 ^ (n + 1) := by
    dsimp [n]
    exact Nat.lt_pow_succ_log_self (by norm_num) L
  have hpowReal :
      (L : ℝ) < ((2 ^ (n + 1) : ℕ) : ℝ) := by
    exact_mod_cast hpowNat
  have hlogL :
      log (L : ℝ) <
        log (((2 ^ (n + 1) : ℕ) : ℝ)) :=
    Real.strictMonoOn_log
      (by
        simpa only [Set.mem_Ioi] using
          (show (0 : ℝ) < (L : ℝ) by positivity))
      (by
        simpa only [Set.mem_Ioi] using
          (show (0 : ℝ) < ((2 ^ (n + 1) : ℕ) : ℝ) by
            positivity))
      hpowReal
  have hlogPow :
      log (((2 ^ (n + 1) : ℕ) : ℝ)) =
        ((n + 1 : ℕ) : ℝ) * log 2 := by
    norm_cast at hlogL ⊢
    simp [Real.log_pow]
  rw [hlogPow] at hlogL
  have hnine' : 9 ≤ n := by simpa [n] using hnine
  have hnineReal : (9 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hnine'
  have hsub :
      ((n - 4 : ℕ) : ℝ) = (n : ℝ) - 4 := by
    rw [Nat.cast_sub (by omega : 4 ≤ n)]
    norm_num
  change log (L : ℝ) / (2 * log 2) ≤ ((n - 4 : ℕ) : ℝ)
  rw [hsub]
  apply (div_le_iff₀ (mul_pos (by norm_num) hlog2)).2
  push_cast at hlogL
  nlinarith

/-- Pointwise absorption of the four scheduled logarithms into the
slightly enlarged power exponent. -/
theorem eventually_mixedBulkProfile_le_absorbed :
    ∀ᶠ j : ℕ in atTop,
      (((j + 1 : ℕ) : ℝ) ^ mixedCanonicalCrossExponent) *
          log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ) ≤
        (((j + 1 : ℕ) : ℝ) ^
          (mixedCanonicalCrossExponent + mixedBulkLogAbsorption)) := by
  filter_upwards
    [eventually_log_add_one_rpow_le_rpow
      (4 : ℝ) mixedBulkLogAbsorption_pos] with j hj
  have hx : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  calc
    (((j + 1 : ℕ) : ℝ) ^ mixedCanonicalCrossExponent) *
          log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ)
        ≤
      (((j + 1 : ℕ) : ℝ) ^ mixedCanonicalCrossExponent) *
        (((j + 1 : ℕ) : ℝ) ^ mixedBulkLogAbsorption) :=
      mul_le_mul_of_nonneg_left hj (Real.rpow_nonneg hx.le _)
    _ = (((j + 1 : ℕ) : ℝ) ^
          (mixedCanonicalCrossExponent + mixedBulkLogAbsorption)) := by
      rw [← Real.rpow_add hx]

/-- Constant arising from the moving-tail integral test and the
conversion from binary to natural logarithms. -/
def mixedBulkMovingTailConstant : ℝ :=
  mixedCanonicalBulkProfileConstant *
    powerTailConstant
      (mixedCanonicalCrossExponent + mixedBulkLogAbsorption) *
    (1 / (2 * log 2)) ^
      (mixedCanonicalCrossExponent + mixedBulkLogAbsorption + 1)

theorem mixedBulkMovingTailConstant_pos :
    0 < mixedBulkMovingTailConstant := by
  unfold mixedBulkMovingTailConstant
  exact mul_pos
    (mul_pos mixedCanonicalBulkProfileConstant_pos
      (powerTailConstant_pos
        mixedCanonicalCross_add_absorption_lt_neg_one))
    (Real.rpow_pos_of_pos
      (by positivity [log_pos (by norm_num : (1 : ℝ) < 2)]) _)

/-- Complete moving-start estimate for the mixed bulk Euler main sum.
The powers outside the odd budget combine to `-2 + δ`. -/
theorem eventually_sum_mixedCanonicalBulkMain_le_moving
    (Kb : ℝ) :
    ∀ᶠ L : ℕ in atTop, ∀ N M : ℕ,
      (∑ j ∈ range M,
        mixedCanonicalBulkMainContribution
          L N Kb (oddBudget L) j) ≤
        mixedCanonicalMainConstant Kb *
          mixedOddWeightBase ^ oddBudget L * (N : ℝ) *
          mixedBulkMovingTailConstant *
          log (L : ℝ) ^ (-2 + mixedBulkLogAbsorption) := by
  rcases eventually_atTop.1
      eventually_mixedBulkProfile_le_absorbed with ⟨H, hH⟩
  filter_upwards
    [eventually_ge_atTop 3,
      eventually_fixed_le_mixedBulkMovingStart (max H 1),
      eventually_ge_atTop (2 ^ 9)] with L hL hstart hL512
  intro N M
  have hlogNat :
      9 ≤ Nat.log 2 L := by
    have h :=
      Nat.log_mono_right (b := 2) hL512
    rw [Nat.log_pow (by norm_num : 1 < 2)] at h
    exact h
  have hstartH : H ≤ mixedBulkMovingStart L :=
    (le_max_left H 1).trans hstart
  have hstart1 : 1 ≤ mixedBulkMovingStart L :=
    (le_max_right H 1).trans hstart
  let C : ℝ :=
    mixedCanonicalMainConstant Kb *
      mixedOddWeightBase ^ oddBudget L * (N : ℝ) *
      log (L : ℝ) ^ mixedCanonicalOuterExponent
  have hlogL : 0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mixedCanonicalMainConstant_pos Kb).le
          (Real.rpow_nonneg
            (by linarith [mixedOddWeightBase_gt_one]) _))
        (Nat.cast_nonneg N))
      (Real.rpow_nonneg hlogL.le _)
  have hpoint :
      ∀ j : ℕ,
        mixedCanonicalBulkMainContribution
            L N Kb (oddBudget L) j ≤
          if L ≤ 16 * dyadicScale j then
            C * mixedCanonicalBulkProfileConstant *
              ((((j + 1 : ℕ) : ℝ) ^
                  mixedCanonicalCrossExponent) *
                log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ))
          else 0 := by
    intro j
    by_cases hnear : L ≤ 16 * dyadicScale j
    · rw [if_pos hnear]
      unfold mixedCanonicalBulkMainContribution
      split_ifs with hj
      · rcases hj with ⟨hdom, _hnear, hgood, hbulk⟩
        simpa [C, mul_assoc] using
          (mixedCanonicalGoodBulkMainBlock_le_profile
            (Kb := Kb) (Ko := oddBudget L)
            hL hdom hnear hgood hbulk)
      · exact mul_nonneg
          (mul_nonneg hC0 mixedCanonicalBulkProfileConstant_pos.le)
          (mul_nonneg
            (Real.rpow_nonneg (by positivity) _)
            (Real.rpow_nonneg (Real.log_natCast_nonneg _) _))
    · rw [if_neg hnear]
      unfold mixedCanonicalBulkMainContribution
      rw [if_neg (by
        intro hj
        exact hnear hj.2.1)]
  have hprofile :
      (∑ j ∈ range M,
          if L ≤ 16 * dyadicScale j then
            (((j + 1 : ℕ) : ℝ) ^ mixedCanonicalCrossExponent) *
              log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ)
          else 0) ≤
        ∑ j ∈ Ico (mixedBulkMovingStart L) M,
          (((j + 1 : ℕ) : ℝ) ^
            (mixedCanonicalCrossExponent + mixedBulkLogAbsorption)) := by
    calc
      _ =
          ∑ j ∈ (range M).filter
              (fun j ↦ L ≤ 16 * dyadicScale j),
            (((j + 1 : ℕ) : ℝ) ^ mixedCanonicalCrossExponent) *
              log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ) := by
          rw [sum_filter]
      _ ≤
          ∑ j ∈ (range M).filter
              (fun j ↦ L ≤ 16 * dyadicScale j),
            (((j + 1 : ℕ) : ℝ) ^
              (mixedCanonicalCrossExponent + mixedBulkLogAbsorption)) := by
          apply sum_le_sum
          intro j hj
          exact hH j
            (hstartH.trans
              (mixedBulkMovingStart_le_of_near
                (mem_filter.mp hj).2))
      _ ≤
          ∑ j ∈ Ico (mixedBulkMovingStart L) M,
            (((j + 1 : ℕ) : ℝ) ^
              (mixedCanonicalCrossExponent + mixedBulkLogAbsorption)) := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro j hj
            rw [mem_filter] at hj
            exact mem_Ico.mpr
              ⟨mixedBulkMovingStart_le_of_near hj.2,
                mem_range.mp hj.1⟩
          · intro j hjIco hjNot
            exact Real.rpow_nonneg (by positivity) _
  have htail :=
    sum_Ico_add_one_rpow_le
      mixedCanonicalCross_add_absorption_lt_neg_one hstart1
      (M := M)
  have hlogStart :=
    log_div_le_mixedBulkMovingStart hL hlogNat
  have hexpNeg :
      mixedCanonicalCrossExponent +
          mixedBulkLogAbsorption + 1 < 0 := by
    linarith [mixedCanonicalCross_add_absorption_lt_neg_one]
  have hlogRatio :
      0 < log (L : ℝ) / (2 * log 2) := by
    positivity [log_pos (by norm_num : (1 : ℝ) < 2)]
  have hinvLogTwoPos :
      0 < (1 / (2 * log 2) : ℝ) := by
    positivity [log_pos (by norm_num : (1 : ℝ) < 2)]
  have hstartPower :
      (mixedBulkMovingStart L : ℝ) ^
          (mixedCanonicalCrossExponent +
            mixedBulkLogAbsorption + 1) ≤
        (1 / (2 * log 2)) ^
            (mixedCanonicalCrossExponent +
              mixedBulkLogAbsorption + 1) *
          log (L : ℝ) ^
            (mixedCanonicalCrossExponent +
              mixedBulkLogAbsorption + 1) := by
    have hanti :=
      Real.rpow_le_rpow_of_nonpos
        hlogRatio hlogStart hexpNeg.le
    calc
      (mixedBulkMovingStart L : ℝ) ^
            (mixedCanonicalCrossExponent +
              mixedBulkLogAbsorption + 1)
          ≤
        (log (L : ℝ) / (2 * log 2)) ^
            (mixedCanonicalCrossExponent +
              mixedBulkLogAbsorption + 1) := hanti
      _ =
        (1 / (2 * log 2)) ^
            (mixedCanonicalCrossExponent +
              mixedBulkLogAbsorption + 1) *
          log (L : ℝ) ^
            (mixedCanonicalCrossExponent +
              mixedBulkLogAbsorption + 1) := by
        rw [show log (L : ℝ) / (2 * log 2) =
            (1 / (2 * log 2)) * log (L : ℝ) by ring,
          Real.mul_rpow hinvLogTwoPos.le hlogL.le]
  have hout :
      mixedCanonicalOuterExponent +
          (mixedCanonicalCrossExponent +
            mixedBulkLogAbsorption + 1) =
        -2 + mixedBulkLogAbsorption := by
    calc
      mixedCanonicalOuterExponent +
            (mixedCanonicalCrossExponent +
              mixedBulkLogAbsorption + 1) =
          (mixedCanonicalOuterExponent +
            (mixedCanonicalDyadicExponent +
              mixedCanonicalResidualExponent + 1)) +
            mixedBulkLogAbsorption := by
              rw [← mixedCanonicalDyadic_add_residualExponent]
              ring
      _ = -2 + mixedBulkLogAbsorption := by
        rw [mixedCanonicalExponent_ledger]
  calc
    (∑ j ∈ range M,
        mixedCanonicalBulkMainContribution
          L N Kb (oddBudget L) j)
        ≤
      ∑ j ∈ range M,
        if L ≤ 16 * dyadicScale j then
          C * mixedCanonicalBulkProfileConstant *
            ((((j + 1 : ℕ) : ℝ) ^
                mixedCanonicalCrossExponent) *
              log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ))
        else 0 := by
          apply sum_le_sum
          intro j hj
          exact hpoint j
    _ =
      (C * mixedCanonicalBulkProfileConstant) *
        (∑ j ∈ range M,
          if L ≤ 16 * dyadicScale j then
            (((j + 1 : ℕ) : ℝ) ^ mixedCanonicalCrossExponent) *
              log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ)
          else 0) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro j hj
        split_ifs <;> ring
    _ ≤
      (C * mixedCanonicalBulkProfileConstant) *
        (∑ j ∈ Ico (mixedBulkMovingStart L) M,
          (((j + 1 : ℕ) : ℝ) ^
            (mixedCanonicalCrossExponent + mixedBulkLogAbsorption))) :=
      mul_le_mul_of_nonneg_left hprofile
        (mul_nonneg hC0 mixedCanonicalBulkProfileConstant_pos.le)
    _ ≤
      (C * mixedCanonicalBulkProfileConstant) *
        (powerTailConstant
            (mixedCanonicalCrossExponent + mixedBulkLogAbsorption) *
          (mixedBulkMovingStart L : ℝ) ^
            (mixedCanonicalCrossExponent +
              mixedBulkLogAbsorption + 1)) :=
      mul_le_mul_of_nonneg_left htail
        (mul_nonneg hC0 mixedCanonicalBulkProfileConstant_pos.le)
    _ ≤
      (C * mixedCanonicalBulkProfileConstant) *
        (powerTailConstant
            (mixedCanonicalCrossExponent + mixedBulkLogAbsorption) *
          ((1 / (2 * log 2)) ^
              (mixedCanonicalCrossExponent +
                mixedBulkLogAbsorption + 1) *
            log (L : ℝ) ^
              (mixedCanonicalCrossExponent +
                mixedBulkLogAbsorption + 1))) := by
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg hC0 mixedCanonicalBulkProfileConstant_pos.le)
      exact mul_le_mul_of_nonneg_left hstartPower
        (powerTailConstant_pos
          mixedCanonicalCross_add_absorption_lt_neg_one).le
    _ =
      mixedCanonicalMainConstant Kb *
          mixedOddWeightBase ^ oddBudget L * (N : ℝ) *
          mixedBulkMovingTailConstant *
          log (L : ℝ) ^ (-2 + mixedBulkLogAbsorption) := by
      unfold C mixedBulkMovingTailConstant
      have hlogCombine :
          log (L : ℝ) ^ mixedCanonicalOuterExponent *
              log (L : ℝ) ^
                (mixedCanonicalCrossExponent +
                  mixedBulkLogAbsorption + 1) =
            log (L : ℝ) ^ (-2 + mixedBulkLogAbsorption) := by
        rw [← Real.rpow_add hlogL, hout]
      rw [show
        mixedCanonicalMainConstant Kb *
              mixedOddWeightBase ^ oddBudget L * (N : ℝ) *
              log (L : ℝ) ^ mixedCanonicalOuterExponent *
              mixedCanonicalBulkProfileConstant *
              (powerTailConstant
                  (mixedCanonicalCrossExponent +
                    mixedBulkLogAbsorption) *
                ((1 / (2 * log 2)) ^
                    (mixedCanonicalCrossExponent +
                      mixedBulkLogAbsorption + 1) *
                  log (L : ℝ) ^
                    (mixedCanonicalCrossExponent +
                      mixedBulkLogAbsorption + 1))) =
            (mixedCanonicalMainConstant Kb *
              mixedOddWeightBase ^ oddBudget L * (N : ℝ) *
              mixedCanonicalBulkProfileConstant *
              powerTailConstant
                (mixedCanonicalCrossExponent +
                  mixedBulkLogAbsorption) *
              (1 / (2 * log 2)) ^
                (mixedCanonicalCrossExponent +
                  mixedBulkLogAbsorption + 1)) *
              (log (L : ℝ) ^ mixedCanonicalOuterExponent *
                log (L : ℝ) ^
                  (mixedCanonicalCrossExponent +
                    mixedBulkLogAbsorption + 1)) by ring,
        hlogCombine]
      ring

/-- The complete moving bulk coefficient is eventually below its allotted
fraction of the rough density. -/
theorem eventually_mixedBulkMovingCoefficient_le_roughDensity
    (Kb : ℝ) :
    ∀ᶠ L : ℕ in atTop,
      mixedCanonicalMainConstant Kb *
          mixedBulkMovingTailConstant *
          mixedOddWeightBase ^ oddBudget L *
          log (L : ℝ) ^ (-2 + mixedBulkLogAbsorption) ≤
        Erdos327.roughDensity L / 64 := by
  let η : ℝ :=
    2 -
      oddBudgetSlope * log mixedOddWeightBase -
      mixedBulkLogAbsorption
  have hη : 1 < η := by
    dsimp [η]
    linarith [mixedOddBudget_add_absorption_lt_one]
  have hC :
      0 ≤ mixedCanonicalMainConstant Kb *
        mixedBulkMovingTailConstant :=
    mul_nonneg (mixedCanonicalMainConstant_pos Kb).le
      mixedBulkMovingTailConstant_pos.le
  have hbase :=
    eventually_const_mul_log_rpow_neg_mul_loglog_rpow_le_roughDensity
      (C := mixedCanonicalMainConstant Kb *
        mixedBulkMovingTailConstant)
      (D := 64) (η := η) (m := 0)
      hC (by norm_num) hη
  filter_upwards [hbase, eventually_ge_atTop 3] with L hbound hL
  have hLreal : (1 : ℝ) < L := by
    exact_mod_cast (show 1 < L by omega)
  have hlogL : 0 < log (L : ℝ) := log_pos hLreal
  rw [oddBudget, base_rpow_mul_loglog
    (by linarith [mixedOddWeightBase_gt_one]) hLreal]
  have hcombine :
      log (L : ℝ) ^
            (oddBudgetSlope * log mixedOddWeightBase) *
          log (L : ℝ) ^ (-2 + mixedBulkLogAbsorption) =
        log (L : ℝ) ^ (-η) := by
    rw [← Real.rpow_add hlogL]
    congr 1
    dsimp [η]
    ring
  calc
    mixedCanonicalMainConstant Kb *
          mixedBulkMovingTailConstant *
          log (L : ℝ) ^
            (oddBudgetSlope * log mixedOddWeightBase) *
          log (L : ℝ) ^ (-2 + mixedBulkLogAbsorption) =
        (mixedCanonicalMainConstant Kb *
          mixedBulkMovingTailConstant) *
          (log (L : ℝ) ^
              (oddBudgetSlope * log mixedOddWeightBase) *
            log (L : ℝ) ^ (-2 + mixedBulkLogAbsorption)) := by
      ring
    _ =
        (mixedCanonicalMainConstant Kb *
          mixedBulkMovingTailConstant) *
          log (L : ℝ) ^ (-η) := by
      rw [hcombine]
    _ =
        (mixedCanonicalMainConstant Kb *
          mixedBulkMovingTailConstant) *
          log (L : ℝ) ^ (-η) *
          log (log (L : ℝ)) ^ (0 : ℝ) := by
      rw [Real.rpow_zero, mul_one]
    _ ≤ Erdos327.roughDensity L / 64 := hbound

/-- Final rough-density allocation for the resolved mixed bulk main
terms, uniform in the ambient cutoff and the finite dyadic endpoint. -/
theorem eventually_sum_mixedCanonicalBulkMain_le_roughDensity
    (Kb : ℝ) :
    ∀ᶠ L : ℕ in atTop, ∀ N M : ℕ,
      (∑ j ∈ range M,
        mixedCanonicalBulkMainContribution
          L N Kb (oddBudget L) j) ≤
        (N : ℝ) * Erdos327.roughDensity L / 64 := by
  filter_upwards
    [eventually_sum_mixedCanonicalBulkMain_le_moving Kb,
      eventually_mixedBulkMovingCoefficient_le_roughDensity Kb]
      with L hsum hcoef
  intro N M
  have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  calc
    (∑ j ∈ range M,
        mixedCanonicalBulkMainContribution
          L N Kb (oddBudget L) j)
        ≤
      mixedCanonicalMainConstant Kb *
          mixedOddWeightBase ^ oddBudget L * (N : ℝ) *
          mixedBulkMovingTailConstant *
          log (L : ℝ) ^ (-2 + mixedBulkLogAbsorption) := hsum N M
    _ =
      (N : ℝ) *
        (mixedCanonicalMainConstant Kb *
          mixedBulkMovingTailConstant *
          mixedOddWeightBase ^ oddBudget L *
          log (L : ℝ) ^ (-2 + mixedBulkLogAbsorption)) := by
      ring
    _ ≤ (N : ℝ) * (Erdos327.roughDensity L / 64) :=
      mul_le_mul_of_nonneg_left hcoef hN0
    _ = (N : ℝ) * Erdos327.roughDensity L / 64 := by
      ring

/-! ## Resolved finite-sieve errors -/

/-- The regularity exponent is strictly larger than the growth exponent
of the moving odd intercept. -/
theorem mixedOddBudgetExponent_lt_regularity :
    oddBudgetSlope * log mixedOddWeightBase <
      mixedCanonicalRegularityExponent := by
  have hqb :
      log (2 : ℝ) < log mixedSourceWeightBase :=
    Real.strictMonoOn_log
      (by norm_num)
      (by
        simpa only [Set.mem_Ioi] using
          (show (0 : ℝ) < mixedSourceWeightBase by
            linarith [mixedSourceWeightBase_gt_one]))
      (by norm_num [mixedSourceWeightBase])
  norm_num [mixedSourceWeightBase] at hqb
  change
    (3.3912 : ℝ) * log (1.34288 : ℝ) <
      (1.000001 : ℝ) * log (2.48933 : ℝ) +
        (1.16312 : ℝ) * log (1.34288 : ℝ)
  norm_num at ⊢
  nlinarith [Real.log_two_gt_d9, Erdos327.log_qo_upper]

/-- The outside coefficient in the resolved sieve-error sum is
eventually below its rough-density allocation. -/
theorem eventually_mixedErrorCoefficient_le_roughDensity
    (Kb : ℝ) :
    ∀ᶠ L : ℕ in atTop,
      mixedCanonicalErrorConstant Kb *
          mixedOddWeightBase ^ oddBudget L *
          log (L : ℝ) ^ mixedCanonicalErrorOuterExponent ≤
        Erdos327.roughDensity L / 64 := by
  let η : ℝ :=
    mixedCanonicalRegularityExponent + 1 -
      oddBudgetSlope * log mixedOddWeightBase
  have hη : 1 < η := by
    dsimp [η]
    linarith [mixedOddBudgetExponent_lt_regularity]
  have hC : 0 ≤ mixedCanonicalErrorConstant Kb :=
    (mixedCanonicalErrorConstant_pos Kb).le
  have hbase :=
    eventually_const_mul_log_rpow_neg_mul_loglog_rpow_le_roughDensity
      (C := mixedCanonicalErrorConstant Kb)
      (D := 64) (η := η) (m := 0)
      hC (by norm_num) hη
  filter_upwards [hbase, eventually_ge_atTop 3] with L hbound hL
  have hLreal : (1 : ℝ) < L := by
    exact_mod_cast (show 1 < L by omega)
  have hlogL : 0 < log (L : ℝ) := log_pos hLreal
  rw [oddBudget, base_rpow_mul_loglog
    (by linarith [mixedOddWeightBase_gt_one]) hLreal]
  have hcombine :
      log (L : ℝ) ^
            (oddBudgetSlope * log mixedOddWeightBase) *
          log (L : ℝ) ^ mixedCanonicalErrorOuterExponent =
        log (L : ℝ) ^ (-η) := by
    rw [← Real.rpow_add hlogL]
    congr 1
    unfold mixedCanonicalErrorOuterExponent
    dsimp [η]
    ring
  calc
    mixedCanonicalErrorConstant Kb *
          log (L : ℝ) ^
            (oddBudgetSlope * log mixedOddWeightBase) *
          log (L : ℝ) ^ mixedCanonicalErrorOuterExponent =
        mixedCanonicalErrorConstant Kb *
          (log (L : ℝ) ^
              (oddBudgetSlope * log mixedOddWeightBase) *
            log (L : ℝ) ^ mixedCanonicalErrorOuterExponent) := by
      ring
    _ = mixedCanonicalErrorConstant Kb *
          log (L : ℝ) ^ (-η) := by
      rw [hcombine]
    _ = mixedCanonicalErrorConstant Kb *
          log (L : ℝ) ^ (-η) *
          log (log (L : ℝ)) ^ (0 : ℝ) := by
      rw [Real.rpow_zero, mul_one]
    _ ≤ Erdos327.roughDensity L / 64 := hbound

/-- Every fixed prefix of good-block sieve errors vanishes once the
roughness cutoff is beyond its largest dyadic scale. -/
theorem mixedCanonicalGoodSieveError_prefix_eq_zero
    {L N J : ℕ} {Kb : ℝ}
    (hfar : dyadicScale J < L) :
    (∑ j ∈ range J,
      mixedCanonicalGoodSieveErrorContribution
        L N Kb (oddBudget L) j) = 0 := by
  apply sum_eq_zero
  intro j hj
  unfold mixedCanonicalGoodSieveErrorContribution
  rw [if_neg]
  intro hgood
  have hjJ : j ≤ J := Nat.le_of_lt (mem_range.mp hj)
  have hscale : dyadicScale j ≤ dyadicScale J :=
    dyadicScale_mono hjJ
  exact (Nat.not_le_of_gt (hscale.trans_lt hfar)) hgood.2.1

/-- Final rough-density allocation for all resolved mixed sieve errors. -/
theorem eventually_sum_mixedCanonicalGoodSieveError_le_roughDensity
    (Kb : ℝ) :
    ∀ᶠ L : ℕ in atTop, ∀ N M : ℕ,
      (∑ j ∈ range M,
        mixedCanonicalGoodSieveErrorContribution
          L N Kb (oddBudget L) j) ≤
        (N : ℝ) * Erdos327.roughDensity L / 64 := by
  obtain ⟨J, htail⟩ :=
    exists_mixedCanonicalGoodSieveError_tail_le
      Kb (ε := 1) (by norm_num)
  filter_upwards
    [eventually_gt_atTop (dyadicScale J),
      eventually_ge_atTop 3,
      eventually_mixedErrorCoefficient_le_roughDensity Kb]
      with L hfar hL hcoef
  intro N M
  have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  by_cases hJM : J ≤ M
  · have hprefix :=
      mixedCanonicalGoodSieveError_prefix_eq_zero
        (N := N) (Kb := Kb) hfar
    calc
      (∑ j ∈ range M,
          mixedCanonicalGoodSieveErrorContribution
            L N Kb (oddBudget L) j) =
        (∑ j ∈ range J,
          mixedCanonicalGoodSieveErrorContribution
            L N Kb (oddBudget L) j) +
        ∑ j ∈ Ico J M,
          mixedCanonicalGoodSieveErrorContribution
            L N Kb (oddBudget L) j :=
          (sum_range_add_sum_Ico _ hJM).symm
      _ =
        ∑ j ∈ Ico J M,
          mixedCanonicalGoodSieveErrorContribution
            L N Kb (oddBudget L) j := by
          rw [hprefix, zero_add]
      _ ≤
        mixedCanonicalErrorConstant Kb *
          mixedOddWeightBase ^ oddBudget L * (N : ℝ) *
          log (L : ℝ) ^ mixedCanonicalErrorOuterExponent := by
          simpa using htail J le_rfl L N M hL
      _ =
        (N : ℝ) *
          (mixedCanonicalErrorConstant Kb *
            mixedOddWeightBase ^ oddBudget L *
            log (L : ℝ) ^ mixedCanonicalErrorOuterExponent) := by
          ring
      _ ≤ (N : ℝ) * (Erdos327.roughDensity L / 64) :=
        mul_le_mul_of_nonneg_left hcoef hN0
      _ = (N : ℝ) * Erdos327.roughDensity L / 64 := by
        ring
  · have hzero :
        (∑ j ∈ range M,
          mixedCanonicalGoodSieveErrorContribution
            L N Kb (oddBudget L) j) = 0 := by
        apply sum_eq_zero
        intro j hj
        unfold mixedCanonicalGoodSieveErrorContribution
        rw [if_neg]
        intro hgood
        have hjJ : j ≤ J := by
          have hjM := mem_range.mp hj
          omega
        have hscale : dyadicScale j ≤ dyadicScale J :=
          dyadicScale_mono hjJ
        exact (Nat.not_le_of_gt (hscale.trans_lt hfar)) hgood.2.1
    rw [hzero]
    exact div_nonneg
      (mul_nonneg hN0 (Erdos327.roughDensity_pos hL).le)
      (by norm_num)

end

end Erdos327.Analytic
