import ErdosProblems.Erdos747.StandardCoordinateInheritance

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

lemma supercritical_mean_lower (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (n M : ℕ)
    (hn : 0 < n) (hM : upperEdgeCount epsilon n ≤ M) :
    Real.log ((3 * n : ℕ) : ℝ) ≤ (M : ℝ) / n :=
  (upperEdgeCount_mean_ge epsilon hepsilon n hn).trans
    (div_le_div_of_nonneg_right (by exact_mod_cast hM) (by positivity))

lemma eventually_standard_upper_spreading_failure_le
    (epsilon zeta kappa : ℝ) (C : ℕ → ℝ)
    (hepsilon : 0 ≤ epsilon) (hzeta : 0 < zeta) (hkappa : 0 < kappa)
    (hC : Tendsto C atTop (𝓝 0)) (hC0 : ∀ᶠ n in atTop, 0 ≤ C n) :
    ∀ᶠ n in atTop, ∀ M : ℕ, upperEdgeCount epsilon n ≤ M →
      finsetProbability (sample n M)
          (fun H ↦ KahnAggregateInsertionGood n M (standardCodegreeCap n M) (C n)
              (aggregateDegreeTolerance n) (aggregateDegreeTolerance n) 32 H ∧
            ¬ GlobalUpperWeightSpread n H (coarseUpperFactor (spreadThinningMultiplier zeta kappa)) zeta) ≤
        4 * Real.exp (-kappa * Real.log ((3 * n : ℕ) : ℝ)) := by
  have hglobal := eventually_aggregate_global_failure_probability_le_exp
    (fun n : ℕ ↦ n) C codegreeRelativeError aggregateDegreeTolerance aggregateDegreeTolerance
    32 zeta kappa tendsto_id (by norm_num) hzeta hkappa hC hC0
    codegreeRelativeError_tendsto_zero eventually_codegreeRelativeError_pos
    aggregateDegreeTolerance_tendsto_zero (Eventually.of_forall aggregateDegreeTolerance_nonneg)
    aggregateDegreeTolerance_tendsto_zero (Eventually.of_forall aggregateDegreeTolerance_nonneg)
  filter_upwards [hglobal, log_vertexCount_tendsto_atTop.eventually_ge_atTop 1,
    eventually_ge_atTop 3] with n hglobaln hlog hn
  intro M hM
  have hmean := supercritical_mean_lower epsilon hepsilon n M (by omega) hM
  have hM0 : 0 < M := by
    by_contra hbad
    have hzero : M = 0 := by omega
    simp only [hzero, Nat.cast_zero, zero_div] at hmean
    linarith only [hmean, hlog]
  have hhalf : halfLogMean n ≤ (M : ℝ) / n := by
    unfold halfLogMean
    linarith only [hmean, hlog]
  exact (hglobaln M (standardCodegreeCap n M) (standardCodegreeCap_pos n M hn hM0) hhalf
    (relativeCodegreeCap_ratio_le_error epsilon hepsilon n M (by omega) hM)).1

lemma eventually_standard_highResidual_spreading_failure_le
    (epsilon a c zeta kappa : ℝ) (C : ℕ → ℝ)
    (hepsilon : 0 ≤ epsilon) (hc : 0 < c) (hc1 : c ≤ 1)
    (hzeta : 0 < zeta) (hkappa : 0 < kappa)
    (hC : Tendsto C atTop (𝓝 0)) (hC0 : ∀ᶠ n in atTop, 0 ≤ C n) :
    ∀ᶠ n in atTop, ∀ M : ℕ, upperEdgeCount epsilon n ≤ M → M ≤ (allEdges n).card →
      finsetProbability (sample n M)
          (fun H ↦ ResidualAggregateInheritanceGood n M
              (coordinateDegreeFloor n M a) (coordinateDegreeCeil n M) (standardCodegreeCap n M)
              c (C n) (residualCountError n (C n) c) (standardResidualDegreeTolerance n)
              (2 * aggregateDegreeTolerance n) 64 H ∧
            ¬ HighResidualLowerSpread n H c (coarseLowerFactor (spreadThinningMultiplier zeta kappa)) zeta) ≤
        (allEdges n).card * (4 * Real.exp (-kappa * Real.log ((3 * (n - 1) : ℕ) : ℝ))) := by
  have hC1 := residualCountError_tendsto_zero C c hC
  have hC10 : ∀ᶠ n in atTop, 0 ≤ residualCountError n (C n) c := by
    filter_upwards [hC0] with n hn
    exact residualCountError_nonneg n (C n) c hn hc hc1
  have hg2 : Tendsto (fun n ↦ 2 * codegreeRelativeError n) atTop (𝓝 0) := by
    simpa only [mul_zero] using codegreeRelativeError_tendsto_zero.const_mul 2
  have hg2pos : ∀ᶠ n in atTop, 0 < 2 * codegreeRelativeError n := by
    filter_upwards [eventually_codegreeRelativeError_pos] with n hn
    positivity
  have heta2 : Tendsto (fun n ↦ 2 * aggregateDegreeTolerance n) atTop (𝓝 0) := by
    simpa only [mul_zero] using aggregateDegreeTolerance_tendsto_zero.const_mul 2
  have heta20 : ∀ᶠ n in atTop, 0 ≤ 2 * aggregateDegreeTolerance n :=
    Eventually.of_forall fun n ↦ mul_nonneg (by norm_num) (aggregateDegreeTolerance_nonneg n)
  have hglobal := eventually_aggregate_global_failure_probability_le_exp
    (fun n : ℕ ↦ n - 1) (fun n ↦ residualCountError n (C n) c)
    (fun n ↦ 2 * codegreeRelativeError n) standardResidualDegreeTolerance
    (fun n ↦ 2 * aggregateDegreeTolerance n) 64 zeta kappa
    (nat_sub_const_tendsto_atTop 1) (by norm_num) hzeta hkappa hC1 hC10 hg2 hg2pos
    standardResidualDegreeTolerance_tendsto_zero (Eventually.of_forall standardResidualDegreeTolerance_nonneg)
    heta2 heta20
  filter_upwards [hglobal, log_vertexCount_tendsto_atTop.eventually_ge_atTop 1,
    eventually_ge_atTop 200] with n hglobaln hlog hn
  intro M hM hMtop
  have hmean := supercritical_mean_lower epsilon hepsilon n M (by omega) hM
  have hmean1 : 1 ≤ (M : ℝ) / n := hlog.trans hmean
  have hM0 : 0 < M := by
    by_contra hbad
    have hzero : M = 0 := by omega
    simp only [hzero, Nat.cast_zero, zero_div] at hmean1
    norm_num at hmean1
  have hcap := standardCodegreeCap_pos n M (by omega) hM0
  have hrelative : (standardCodegreeCap n M : ℝ) / ((M : ℝ) / n) ≤ codegreeRelativeError n :=
    relativeCodegreeCap_ratio_le_error epsilon hepsilon n M (by omega) hM
  apply residualAggregate_highResidual_failure_probability_le (by omega : 2 ≤ n) hM0 hMtop hc (by positivity)
  intro j hj hjM
  have hjmean := coordinate_residual_layer_halfLogMean n M j hn hmean1 hmean hj
  have hjcap := coordinate_residual_layer_relative_cap n M j (standardCodegreeCap n M)
    (codegreeRelativeError n) hn hmean1 hj hrelative
  have hraw := (hglobaln j (standardCodegreeCap n M) hcap hjmean hjcap).2
  calc
    _ = finsetProbability (sample (n - 1) j)
        (fun H ↦ KahnAggregateInsertionGood (n - 1) j (standardCodegreeCap n M)
            (residualCountError n (C n) c) (standardResidualDegreeTolerance n)
            (2 * aggregateDegreeTolerance n) 64 H ∧
          ¬ GlobalLowerWeightSpread (n - 1) H
            (coarseLowerFactor (spreadThinningMultiplier zeta kappa)) zeta) := by
      apply finsetProbability_congr_event
      intro H hHs
      simp only [KahnAggregateInsertionLowerFailure, (mem_sample.mp hHs).2]
    _ ≤ _ := hraw

end

end Erdos747
