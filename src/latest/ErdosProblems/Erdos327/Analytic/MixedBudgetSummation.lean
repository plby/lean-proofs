import ErdosProblems.Erdos327.Analytic.MixedTerminalSummation

/-!
# Arbitrary budget allocations for the mixed scheduled sum

The first conclusion needs the bulk main term, finite-sieve error,
terminal term, boundary term, and the exceptional endpoint all to fit
inside one `1 / 64` density budget.  The earlier summation modules record
convenient `1 / 64` estimates for each analytic piece separately.  This
module exposes the same decay estimates with an arbitrary positive
denominator, so the pieces can be combined without losing constants.
-/

namespace Erdos327.Analytic

open Filter Finset Real Topology

open scoped BigOperators

noncomputable section

/-- The moving bulk coefficient fits an arbitrary positive fraction of
the rough density. -/
theorem eventually_mixedBulkMovingCoefficient_le_roughDensity_div
    (Kb D : ℝ) (hD : 0 < D) :
    ∀ᶠ L : ℕ in atTop,
      mixedCanonicalMainConstant Kb *
          mixedBulkMovingTailConstant *
          mixedOddWeightBase ^ oddBudget L *
          log (L : ℝ) ^ (-2 + mixedBulkLogAbsorption) ≤
        Erdos327.roughDensity L / D := by
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
      (D := D) (η := η) (m := 0)
      hC hD hη
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
    _ ≤ Erdos327.roughDensity L / D := hbound

/-- All resolved mixed bulk main terms fit an arbitrary positive density
allocation, uniformly in the ambient cutoff and summation endpoint. -/
theorem eventually_sum_mixedCanonicalBulkMain_le_roughDensity_div
    (Kb D : ℝ) (hD : 0 < D) :
    ∀ᶠ L : ℕ in atTop, ∀ N M : ℕ,
      (∑ j ∈ range M,
        mixedCanonicalBulkMainContribution
          L N Kb (oddBudget L) j) ≤
        (N : ℝ) * Erdos327.roughDensity L / D := by
  filter_upwards
    [eventually_sum_mixedCanonicalBulkMain_le_moving Kb,
      eventually_mixedBulkMovingCoefficient_le_roughDensity_div
        Kb D hD] with L hsum hcoef
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
    _ ≤ (N : ℝ) * (Erdos327.roughDensity L / D) :=
      mul_le_mul_of_nonneg_left hcoef hN0
    _ = (N : ℝ) * Erdos327.roughDensity L / D := by
      ring

/-- The resolved sieve-error coefficient fits an arbitrary positive
fraction of the rough density. -/
theorem eventually_mixedErrorCoefficient_le_roughDensity_div
    (Kb D : ℝ) (hD : 0 < D) :
    ∀ᶠ L : ℕ in atTop,
      mixedCanonicalErrorConstant Kb *
          mixedOddWeightBase ^ oddBudget L *
          log (L : ℝ) ^ mixedCanonicalErrorOuterExponent ≤
        Erdos327.roughDensity L / D := by
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
      (D := D) (η := η) (m := 0)
      hC hD hη
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
    _ ≤ Erdos327.roughDensity L / D := hbound

/-- All resolved finite-sieve errors fit an arbitrary positive density
allocation. -/
theorem eventually_sum_mixedCanonicalGoodSieveError_le_roughDensity_div
    (Kb D : ℝ) (hD : 0 < D) :
    ∀ᶠ L : ℕ in atTop, ∀ N M : ℕ,
      (∑ j ∈ range M,
        mixedCanonicalGoodSieveErrorContribution
          L N Kb (oddBudget L) j) ≤
        (N : ℝ) * Erdos327.roughDensity L / D := by
  obtain ⟨J, htail⟩ :=
    exists_mixedCanonicalGoodSieveError_tail_le
      Kb (ε := 1) (by norm_num)
  filter_upwards
    [eventually_gt_atTop (dyadicScale J),
      eventually_ge_atTop 3,
      eventually_mixedErrorCoefficient_le_roughDensity_div Kb D hD]
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
      _ ≤ (N : ℝ) * (Erdos327.roughDensity L / D) :=
        mul_le_mul_of_nonneg_left hcoef hN0
      _ = (N : ℝ) * Erdos327.roughDensity L / D := by
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
      hD.le

/-- The good terminal Euler-main sum fits an arbitrary positive density
allocation after the roughness cutoff is fixed and the ambient cutoff
is sufficiently large. -/
theorem eventually_sum_mixedCanonicalTerminalMain_le_roughDensity_div
    (Kb D : ℝ) (hD : 0 < D) :
    ∀ᶠ L : ℕ in atTop, ∀ᶠ N : ℕ in atTop, ∀ M : ℕ,
      (∑ j ∈ range M,
        mixedCanonicalTerminalMainContribution
          L N Kb (oddBudget L) j) ≤
        (N : ℝ) * Erdos327.roughDensity L / D := by
  rcases eventually_atTop.1
      eventually_mixedTerminalProfile_absorbed with ⟨H, hH⟩
  filter_upwards
    [eventually_ge_atTop 3,
      eventually_fixed_le_mixedBulkMovingStart H] with L hL hstart
  let C₀ : ℝ :=
    mixedCanonicalMainConstant Kb *
      mixedOddWeightBase ^ oddBudget L *
      log (L : ℝ) ^ mixedCanonicalOuterExponent *
      mixedCanonicalTerminalProfileConstant *
      mixedTerminalConvolutionConstant
  have hpower := tendsto_mixedTerminalConvolutionPower_zero
  have hscaled :
      Tendsto
        (fun N : ℕ ↦
          C₀ * (((Nat.log 2 N + 1 : ℕ) : ℝ) ^
            (mixedTerminalAbsorbedDyadicExponent +
              mixedCanonicalResidualExponent + 1)))
        atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hpower)
  have htarget :
      0 < Erdos327.roughDensity L / D :=
    div_pos (Erdos327.roughDensity_pos hL) hD
  filter_upwards
    [(tendsto_order.1 hscaled).2
      (Erdos327.roughDensity L / D) htarget] with N hN
  intro M
  let C : ℝ :=
    mixedCanonicalMainConstant Kb *
      mixedOddWeightBase ^ oddBudget L * (N : ℝ) *
      log (L : ℝ) ^ mixedCanonicalOuterExponent *
      mixedCanonicalTerminalProfileConstant
  have hC0 : 0 ≤ C := by
    dsimp [C]
    have hlogL :
        0 < log (L : ℝ) :=
      log_pos (by exact_mod_cast (show 1 < L by omega))
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (mixedCanonicalMainConstant_pos Kb).le
            (Real.rpow_nonneg
              (by linarith [mixedOddWeightBase_gt_one]) _))
          (Nat.cast_nonneg N))
        (Real.rpow_nonneg hlogL.le _))
      mixedCanonicalTerminalProfileConstant_pos.le
  have hsumEq :
      (∑ j ∈ range M,
          mixedCanonicalTerminalMainContribution
            L N Kb (oddBudget L) j) =
        ∑ j ∈ mixedCanonicalTerminalIndexSet L N M,
          mixedCanonicalTerminalMainContribution
            L N Kb (oddBudget L) j := by
    unfold mixedCanonicalTerminalIndexSet
      mixedCanonicalTerminalMainContribution
    rw [sum_filter]
    apply sum_congr rfl
    intro j hj
    by_cases hp :
        32 * sieveRadius j ≤ j ∧
          L ≤ 16 * dyadicScale j ∧
          mixedScheduledGoodIndex L N j ∧
          N / (dyadicScale j * dyadicScale j) < dyadicScale j
    · rw [if_pos hp, if_pos hp]
    · rw [if_neg hp, if_neg hp]
  have hpoint :
      ∀ j : ℕ,
        mixedCanonicalTerminalMainContribution
            L N Kb (oddBudget L) j ≤
          C *
            ((((j + 1 : ℕ) : ℝ) ^
                mixedCanonicalDyadicExponent) *
              (((dyadicResidualIndex N j + 1 : ℕ) : ℝ) ^
                mixedCanonicalResidualExponent) *
              log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ)) := by
    intro j
    simpa [C, mul_assoc] using
      (mixedCanonicalTerminalMainContribution_le_profile
        (L := L) (N := N) (j := j)
        (Kb := Kb) (Ko := oddBudget L) hL)
  have hprofile :=
    sum_mixedTerminalIndexSet_profile_le
      (L := L) (N := N) (M := M) hL hstart hH
  have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  calc
    (∑ j ∈ range M,
        mixedCanonicalTerminalMainContribution
          L N Kb (oddBudget L) j) =
      ∑ j ∈ mixedCanonicalTerminalIndexSet L N M,
        mixedCanonicalTerminalMainContribution
          L N Kb (oddBudget L) j := hsumEq
    _ ≤
      ∑ j ∈ mixedCanonicalTerminalIndexSet L N M,
        C *
          ((((j + 1 : ℕ) : ℝ) ^
              mixedCanonicalDyadicExponent) *
            (((dyadicResidualIndex N j + 1 : ℕ) : ℝ) ^
              mixedCanonicalResidualExponent) *
            log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ)) := by
      apply sum_le_sum
      intro j hj
      exact hpoint j
    _ =
      C *
        (∑ j ∈ mixedCanonicalTerminalIndexSet L N M,
          (((j + 1 : ℕ) : ℝ) ^
              mixedCanonicalDyadicExponent) *
            (((dyadicResidualIndex N j + 1 : ℕ) : ℝ) ^
              mixedCanonicalResidualExponent) *
            log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ)) := by
      rw [mul_sum]
    _ ≤
      C * (mixedTerminalConvolutionConstant *
        (((Nat.log 2 N + 1 : ℕ) : ℝ) ^
          (mixedTerminalAbsorbedDyadicExponent +
            mixedCanonicalResidualExponent + 1))) :=
      mul_le_mul_of_nonneg_left hprofile hC0
    _ =
      (N : ℝ) *
        (C₀ * (((Nat.log 2 N + 1 : ℕ) : ℝ) ^
          (mixedTerminalAbsorbedDyadicExponent +
            mixedCanonicalResidualExponent + 1))) := by
      dsimp [C, C₀]
      ring
    _ ≤
      (N : ℝ) * (Erdos327.roughDensity L / D) :=
      mul_le_mul_of_nonneg_left hN.le hN0
    _ = (N : ℝ) * Erdos327.roughDensity L / D := by
      ring

end

end Erdos327.Analytic
