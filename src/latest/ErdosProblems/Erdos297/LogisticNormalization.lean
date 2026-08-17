/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos297.Statement
import ErdosProblems.Erdos297.Riemann
import ErdosProblems.Erdos297.Parameters
import ErdosProblems.Erdos297.DeletedSetSums
import ErdosProblems.Erdos297.GoodSetDensity

/-!
# Normalizing the logistic product measure

This file carries out the deterministic normalization step in the
Liu--Sawhney lower bound.  We restrict the sampled critical logistic profile
to the finite good set, prove that its retained reciprocal expectation tends
to one, and multiply every marginal by the reciprocal of that expectation.
The resulting marginals have *exactly* the required reciprocal expectation.

The last section gives one error, tending to zero, which uniformly controls
both selected and omitted log-likelihoods after the common rescaling.
-/

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos297.LogisticNormalization

noncomputable section

open Erdos297.GoodFactorization

attribute [local instance] Classical.propDecidable

/-- The finite set retained by the arithmetic part of the lower bound. -/
def goodSet (N : ℕ) : Finset ℕ :=
  goodDenominators N (M N) (S N)

/-- The continuum critical profile sampled at `n / N`. -/
def rawLogisticProbability (lam : ℝ) (N n : ℕ) : ℝ :=
  selectionProbability lam ((n : ℝ) / N)

/-- The reciprocal expectation retained on the good set. -/
def rawReciprocalMean (lam : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ goodSet N, rawLogisticProbability lam N n / n

/-- The common multiplier which makes the retained reciprocal expectation
exactly one. -/
def normalizationFactor (lam : ℝ) (N : ℕ) : ℝ :=
  (rawReciprocalMean lam N)⁻¹

/-- The normalized logistic marginal. -/
def normalizedLogisticProbability (lam : ℝ) (N n : ℕ) : ℝ :=
  normalizationFactor lam N * rawLogisticProbability lam N n

/-- The deleted portion of `[1,N]`. -/
def deletedSet (N : ℕ) : Finset ℕ :=
  Icc 1 N \ goodSet N

/-- The critical parameter is positive. -/
lemma criticalParameter_pos {lam : ℝ} (hlam : IsUniqueCriticalParameter lam) :
    0 < lam :=
  hlam.1.1

lemma rawLogisticProbability_nonneg (lam : ℝ) (N n : ℕ) :
    0 ≤ rawLogisticProbability lam N n :=
  DeletedSetSums.selectionProbability_nonneg _ _

lemma rawLogisticProbability_le_one (lam : ℝ) (N n : ℕ) :
    rawLogisticProbability lam N n ≤ 1 :=
  DeletedSetSums.selectionProbability_le_one _ _

lemma rawLogisticProbability_pos {lam : ℝ} {N n : ℕ}
    (hN : 0 < N) (hn : 0 < n) :
    0 < rawLogisticProbability lam N n := by
  rw [rawLogisticProbability, selectionProbability, if_neg (by positivity)]
  positivity

/-- A positive parameter makes every sampled marginal at most one half. -/
lemma rawLogisticProbability_le_half {lam : ℝ} (hlam : 0 < lam)
    {N n : ℕ} (hN : 0 < N) (hn : 0 < n) :
    rawLogisticProbability lam N n ≤ 1 / 2 := by
  rw [rawLogisticProbability, selectionProbability, if_neg (by positivity)]
  have hexp : 1 ≤ Real.exp (lam / ((n : ℝ) / N)) := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    positivity
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 1 +
    Real.exp (lam / ((n : ℝ) / N)))]
  linarith

/-- On `[0,1]` the endpoint-extended moment kernel has a uniform norm bound. -/
lemma exists_norm_momentKernel_bound {lam : ℝ} (hlam : 0 < lam) :
    ∃ C : ℝ, ∀ x ∈ Icc (0 : ℝ) 1, ‖momentKernel lam x‖ ≤ C := by
  have hcompact : IsCompact
      ((fun x : ℝ ↦ ‖momentKernel lam x‖) '' Icc (0 : ℝ) 1) :=
    isCompact_Icc.image_of_continuousOn
      (continuousOn_momentKernel hlam).norm
  rcases hcompact.bddAbove with ⟨C, hC⟩
  refine ⟨C, fun x hx ↦ ?_⟩
  exact hC (mem_image_of_mem _ hx)

lemma momentKernel_div_scale {lam : ℝ} {N n : ℕ}
    (hN : 0 < N) (hn : 0 < n) :
    momentKernel lam ((n : ℝ) / N) / N =
      rawLogisticProbability lam N n / n := by
  rw [momentKernel, if_neg (by positivity)]
  simp only [rawLogisticProbability]
  field_simp

/-- Exact normalization, assuming only that the retained mean is nonzero. -/
theorem normalized_reciprocal_mean_eq_one {lam : ℝ} {N : ℕ}
    (hne : rawReciprocalMean lam N ≠ 0) :
    ∑ n ∈ goodSet N, normalizedLogisticProbability lam N n / n = 1 := by
  simp only [normalizedLogisticProbability, mul_div_assoc, ← Finset.mul_sum,
    normalizationFactor, rawReciprocalMean]
  exact inv_mul_cancel₀ hne

/-! ## Convergence of the retained expectation -/

lemma deletedSet_card_isLittleO :
    (fun N : ℕ ↦ ((deletedSet N).card : ℝ))
      =o[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
  simpa [deletedSet, goodSet,
    GoodSetDensity.sourceGoodDenominators,
    GoodSetDensity.deletedSourceDenominators] using
      GoodSetDensity.deletedSourceDenominators_card_isLittleO

lemma eventually_goodSet_subset_Icc :
    ∀ᶠ N : ℕ in atTop, goodSet N ⊆ Icc 1 N := by
  simpa [goodSet, GoodSetDensity.sourceGoodDenominators] using
    GoodSetDensity.eventually_sourceGoodDenominators_subset_denominators

/-- The normalized sum of the deleted moment-kernel values tends to zero. -/
lemma tendsto_deleted_momentKernel_sum_div {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun N : ℕ ↦
      (∑ n ∈ deletedSet N, momentKernel lam ((n : ℝ) / N)) / N)
      atTop (nhds 0) := by
  obtain ⟨C, hC⟩ := exists_norm_momentKernel_bound hlam
  apply DeletedSetSums.tendsto_sum_div_of_card_isLittleO
    deletedSet (fun N n ↦ momentKernel lam ((n : ℝ) / N)) C
    deletedSet_card_isLittleO
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN n hn
  have hnIcc : n ∈ Finset.Icc 1 N := (mem_sdiff.mp hn).1
  apply hC
  exact ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
    (div_le_one (by exact_mod_cast hN)).2
      (by exact_mod_cast (Finset.mem_Icc.mp hnIcc).2)⟩

/-- Restricting the critical sampled profile to the good set does not change
its limiting reciprocal expectation. -/
theorem tendsto_rawReciprocalMean {lam : ℝ}
    (hlam : IsUniqueCriticalParameter lam) :
    Tendsto (rawReciprocalMean lam) atTop (nhds 1) := by
  have hlampos : 0 < lam := criticalParameter_pos hlam
  have hfull : Tendsto
      (fun N : ℕ ↦ ∑ n ∈ Icc 1 N,
        rawLogisticProbability lam N n / (n : ℝ))
      atTop (nhds 1) := by
    simpa only [rawLogisticProbability, hlam.1.2] using
      tendsto_sum_Icc_selectionProbability_div hlampos
  have hdeleted := tendsto_deleted_momentKernel_sum_div hlampos
  have hlim := hfull.sub hdeleted
  simp only [sub_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_goodSet_subset_Icc,
    eventually_gt_atTop (0 : ℕ)] with N hsub hN
  have hsum := Finset.sum_sdiff hsub
    (f := fun n : ℕ ↦ rawLogisticProbability lam N n / (n : ℝ))
  have hdeletedEq :
      (∑ n ∈ deletedSet N, momentKernel lam ((n : ℝ) / N)) / N =
        ∑ n ∈ deletedSet N,
          rawLogisticProbability lam N n / (n : ℝ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro n hn
    exact momentKernel_div_scale hN
      ((Finset.mem_Icc.mp (Finset.mem_sdiff.mp hn).1).1.trans_lt' Nat.zero_lt_one)
  rw [rawReciprocalMean, hdeletedEq]
  simpa [deletedSet] using (show
    (∑ n ∈ Icc 1 N, rawLogisticProbability lam N n / (n : ℝ)) -
        ∑ n ∈ Icc 1 N \ goodSet N,
          rawLogisticProbability lam N n / (n : ℝ) =
      ∑ n ∈ goodSet N,
        rawLogisticProbability lam N n / (n : ℝ) by linarith)

/-- The common normalization factor tends to one. -/
theorem tendsto_normalizationFactor {lam : ℝ}
    (hlam : IsUniqueCriticalParameter lam) :
    Tendsto (normalizationFactor lam) atTop (nhds 1) := by
  change Tendsto (fun N ↦ (rawReciprocalMean lam N)⁻¹) atTop (nhds 1)
  simpa only [inv_one] using
    (tendsto_rawReciprocalMean hlam).inv₀ one_ne_zero

theorem eventually_rawReciprocalMean_ne_zero {lam : ℝ}
    (hlam : IsUniqueCriticalParameter lam) :
    ∀ᶠ N : ℕ in atTop, rawReciprocalMean lam N ≠ 0 :=
  (tendsto_rawReciprocalMean hlam).eventually (isOpen_ne.mem_nhds one_ne_zero)

theorem eventually_normalizationFactor_pos {lam : ℝ}
    (hlam : IsUniqueCriticalParameter lam) :
    ∀ᶠ N : ℕ in atTop, 0 < normalizationFactor lam N :=
  (tendsto_normalizationFactor hlam).eventually (eventually_gt_nhds zero_lt_one)

theorem eventually_normalizationFactor_bounds {lam : ℝ}
    (hlam : IsUniqueCriticalParameter lam) :
    ∀ᶠ N : ℕ in atTop,
      1 / 2 ≤ normalizationFactor lam N ∧
        normalizationFactor lam N ≤ 3 / 2 := by
  have h := (tendsto_normalizationFactor hlam).eventually
    (Metric.ball_mem_nhds (1 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [h] with N hN
  rw [Real.dist_eq] at hN
  constructor <;> linarith [abs_lt.mp hN]

/-- The normalized probabilities have exact reciprocal expectation one for
all sufficiently large scales. -/
theorem eventually_normalized_reciprocal_mean_eq_one {lam : ℝ}
    (hlam : IsUniqueCriticalParameter lam) :
    ∀ᶠ N : ℕ in atTop,
      ∑ n ∈ goodSet N, normalizedLogisticProbability lam N n / n = 1 :=
  (eventually_rawReciprocalMean_ne_zero hlam).mono fun _N hN ↦
    normalized_reciprocal_mean_eq_one hN

/-! ## The retained free energy -/

/-- The finite log-partition summand, written using the endpoint-extended
kernel so its Riemann-sum origin is literal. -/
def rawLogPartition (lam : ℝ) (N n : ℕ) : ℝ :=
  freeEnergyKernel lam ((n : ℝ) / N)

lemma tendsto_full_rawLogPartition_sum_div {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun N : ℕ ↦
      (∑ n ∈ Icc 1 N, rawLogPartition lam N n) / N)
      atTop (nhds (gamma lam - lam)) := by
  have h := tendsto_rightRiemannSum_freeEnergyKernel hlam
  have heq :
      (fun N : ℕ ↦ (∑ n ∈ Icc 1 N, rawLogPartition lam N n) / N)
        =ᶠ[atTop] rightRiemannSum (freeEnergyKernel lam) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    symm
    rw [← Finset.Ico_succ_right_eq_Icc 1 N]
    change rightRiemannSum (freeEnergyKernel lam) N =
      (∑ n ∈ Ico 1 (N + 1), rawLogPartition lam N n) / N
    rw [← Finset.sum_Ico_add (fun n : ℕ ↦ rawLogPartition lam N n) 0 N 1]
    simp only [Nat.Ico_zero_eq_range, rightRiemannSum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [rawLogPartition]
    congr 2
    congr 1
    ring
  have hlim := h.congr' heq.symm
  convert hlim using 1
  congr 1
  simp only [gamma]
  ring

lemma tendsto_deleted_rawLogPartition_sum_div {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun N : ℕ ↦
      (∑ n ∈ deletedSet N, rawLogPartition lam N n) / N)
      atTop (nhds 0) := by
  apply DeletedSetSums.tendsto_sum_div_of_card_isLittleO
    deletedSet (fun N n ↦ rawLogPartition lam N n) (Real.log 2)
    deletedSet_card_isLittleO
  filter_upwards with N n hn
  exact DeletedSetSums.norm_freeEnergyKernel_le_log_two hlam.le
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-- Removing the density-zero exceptional set preserves the normalized
free-energy limit. -/
theorem tendsto_retained_rawLogPartition_sum_div {lam : ℝ}
    (hlam : IsUniqueCriticalParameter lam) :
    Tendsto (fun N : ℕ ↦
      (∑ n ∈ goodSet N, rawLogPartition lam N n) / N)
      atTop (nhds (gamma lam - lam)) := by
  have hfull := tendsto_full_rawLogPartition_sum_div (criticalParameter_pos hlam)
  have hdeleted := tendsto_deleted_rawLogPartition_sum_div
    (criticalParameter_pos hlam)
  have hlim := hfull.sub hdeleted
  simp only [sub_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_goodSet_subset_Icc] with N hsub
  have hsum := Finset.sum_sdiff hsub (f := rawLogPartition lam N)
  simp only [deletedSet]
  rw [← sub_div]
  congr 1
  linarith

/-! ## Source probability bounds -/

/-- At the lower endpoint `M`, the logistic denominator is eventually at
most half of `log log N`.  This is the quantitative estimate behind the
source lower bound on every marginal. -/
lemma eventually_logisticDenominator_le_half_logLog {lam : ℝ} (hlam : 0 < lam) :
    ∀ᶠ N : ℕ in atTop, ∀ n ∈ goodSet N,
      1 + Real.exp (lam / ((n : ℝ) / N)) ≤ logLogScale N / 2 := by
  let T : ℝ := max ((4 * lam) ^ 2) (2 * Real.log 3)
  have hlarge := tendsto_logLogLogScale.eventually_ge_atTop T
  filter_upwards [hlarge, eventually_pos_scales,
    eventually_real_scales_ge_two] with N hT hscales hnscales n hn
  rcases hscales with ⟨hNpos, hlog, hLL, htpos⟩
  have hN : 0 < N := by exact_mod_cast hNpos
  have ht0 : 0 ≤ logLogLogScale N := htpos.le
  have hsqrtpos : 0 < Real.sqrt (logLogLogScale N) := Real.sqrt_pos.2 htpos
  have hMhalf : MReal N / 2 ≤ (M N : ℝ) :=
    half_le_floor hnscales.2.2
  have hgood := mem_goodDenominators.mp hn
  have hnLower : (M N : ℝ) ≤ n := by exact_mod_cast hgood.1
  have hnUpper : (n : ℝ) ≤ N := by exact_mod_cast hgood.2.1
  have hnpos : 0 < n := by
    have hMone : (1 : ℝ) ≤ M N := by
      have : (1 : ℝ) ≤ MReal N / 2 := by linarith [hnscales.2.2]
      exact this.trans hMhalf
    exact_mod_cast lt_of_lt_of_le (zero_lt_one : (0 : ℝ) < 1)
      (hMone.trans hnLower)
  have hratio : (N : ℝ) / n ≤ 2 * Real.sqrt (logLogLogScale N) := by
    have hlow : (N : ℝ) / (2 * Real.sqrt (logLogLogScale N)) ≤ n := by
      calc
        (N : ℝ) / (2 * Real.sqrt (logLogLogScale N)) = MReal N / 2 := by
          rw [MReal]
          ring
        _ ≤ (M N : ℝ) := hMhalf
        _ ≤ n := hnLower
    rw [div_le_iff₀ (by exact_mod_cast hnpos)]
    have hcross := (div_le_iff₀ (mul_pos (by norm_num) hsqrtpos)).mp hlow
    nlinarith
  have hsqrtLam : 4 * lam ≤ Real.sqrt (logLogLogScale N) := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ 4 * lam)]
    apply Real.sqrt_le_sqrt
    exact (le_max_left _ _).trans hT
  have hexponent :
      lam / ((n : ℝ) / N) ≤ logLogLogScale N / 2 := by
    have heq : lam / ((n : ℝ) / N) = lam * ((N : ℝ) / n) := by
      field_simp
    rw [heq]
    have hmul := mul_le_mul_of_nonneg_left hratio hlam.le
    have hsqrtSq := Real.sq_sqrt ht0
    nlinarith
  have hlogThree : Real.log 3 ≤ logLogLogScale N / 2 := by
    have := (le_max_right ((4 * lam) ^ 2) (2 * Real.log 3)).trans hT
    linarith
  have hy : (3 : ℝ) ≤ Real.exp (logLogLogScale N / 2) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    exact Real.exp_le_exp.mpr hlogThree
  have hexp : Real.exp (lam / ((n : ℝ) / N)) ≤
      Real.exp (logLogLogScale N / 2) :=
    Real.exp_le_exp.mpr hexponent
  have hLLexp : Real.exp (logLogLogScale N) = logLogScale N := by
    exact Real.exp_log (zero_lt_one.trans hLL)
  calc
    1 + Real.exp (lam / ((n : ℝ) / N)) ≤
        1 + Real.exp (logLogLogScale N / 2) := by linarith
    _ ≤ Real.exp (logLogLogScale N / 2) ^ 2 / 2 := by nlinarith
    _ = Real.exp (logLogLogScale N) / 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 2
      ring
    _ = logLogScale N / 2 := by rw [hLLexp]

lemma eventually_rawLogisticProbability_lower {lam : ℝ} (hlam : 0 < lam) :
  ∀ᶠ N : ℕ in atTop, ∀ n ∈ goodSet N,
      2 / logLogScale N ≤ rawLogisticProbability lam N n := by
  filter_upwards [eventually_logisticDenominator_le_half_logLog hlam,
    eventually_pos_scales, eventually_real_scales_ge_two] with
      N hden hscales hreal n hn
  rcases hscales with ⟨hN, hlog, hLL, ht⟩
  have hnpos : 0 < n := by
    have hgood := mem_goodDenominators.mp hn
    have hMhalf := half_le_floor hreal.2.2
    have hMone : (1 : ℝ) ≤ M N :=
      (show (1 : ℝ) ≤ MReal N / 2 by linarith [hreal.2.2]).trans hMhalf
    exact_mod_cast lt_of_lt_of_le (zero_lt_one : (0 : ℝ) < 1)
      (hMone.trans (by exact_mod_cast hgood.1 : (M N : ℝ) ≤ n))
  rw [rawLogisticProbability, selectionProbability, if_neg (by positivity)]
  have hLLpos : 0 < logLogScale N := zero_lt_one.trans hLL
  have hdenpos : 0 < 1 + Real.exp (lam / ((n : ℝ) / N)) := by positivity
  rw [div_le_div_iff₀ hLLpos hdenpos]
  have := hden n hn
  nlinarith

/-- A fixed gap below one half, uniform over `n ≤ N`. -/
lemma rawLogisticProbability_le_endpoint {lam : ℝ} (hlam : 0 < lam)
    {N n : ℕ} (hN : 0 < N) (hn : 0 < n) (hnN : n ≤ N) :
    rawLogisticProbability lam N n ≤ 1 / (1 + Real.exp lam) := by
  rw [rawLogisticProbability, selectionProbability, if_neg (by positivity)]
  apply one_div_le_one_div_of_le (by positivity)
  have hratio : (1 : ℝ) ≤ (N : ℝ) / n := by
    rw [le_div_iff₀ (by exact_mod_cast hn)]
    norm_num
    exact_mod_cast hnN
  have heq : lam / ((n : ℝ) / N) = lam * ((N : ℝ) / n) := by
    field_simp
  rw [heq]
  have hexponent : lam ≤ lam * ((N : ℝ) / n) := by nlinarith
  simpa only [add_comm] using
    (add_le_add_left (Real.exp_le_exp.mpr hexponent) 1)

/-- The exact source interval for every normalized marginal. -/
theorem eventually_normalized_probability_bounds {lam : ℝ}
    (hlam : IsUniqueCriticalParameter lam) :
    ∀ᶠ N : ℕ in atTop, ∀ n ∈ goodSet N,
      1 / logLogScale N ≤ normalizedLogisticProbability lam N n ∧
        normalizedLogisticProbability lam N n ≤ 1 / 2 := by
  have hlampos := criticalParameter_pos hlam
  have halphaEndpoint :
      ∀ᶠ N : ℕ in atTop,
        normalizationFactor lam N ≤ (1 + Real.exp lam) / 2 := by
    have : 1 < Real.exp lam := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr hlampos
    have hc : (1 : ℝ) < (1 + Real.exp lam) / 2 := by linarith
    exact (tendsto_normalizationFactor hlam).eventually (eventually_le_nhds hc)
  filter_upwards [eventually_normalizationFactor_bounds hlam,
    halphaEndpoint, eventually_rawLogisticProbability_lower hlampos,
    eventually_pos_scales, eventually_real_scales_ge_two] with
      N halpha halphaEnd hpLower hscales hreal n hn
  rcases hscales with ⟨hNreal, hlog, hLL, ht⟩
  have hN : 0 < N := by exact_mod_cast hNreal
  have hgood := mem_goodDenominators.mp hn
  have hnpos : 0 < n := by
    have hMhalf := half_le_floor hreal.2.2
    have hMone : (1 : ℝ) ≤ M N :=
      (show (1 : ℝ) ≤ MReal N / 2 by linarith [hreal.2.2]).trans hMhalf
    exact_mod_cast lt_of_lt_of_le (zero_lt_one : (0 : ℝ) < 1)
      (hMone.trans (by exact_mod_cast hgood.1 : (M N : ℝ) ≤ n))
  have hpUpper := rawLogisticProbability_le_endpoint hlampos hN hnpos hgood.2.1
  have hLLpos : 0 < logLogScale N := zero_lt_one.trans hLL
  constructor
  · rw [normalizedLogisticProbability]
    calc
      1 / logLogScale N = (1 / 2 : ℝ) * (2 / logLogScale N) := by ring
      _ ≤ normalizationFactor lam N * rawLogisticProbability lam N n := by
        exact mul_le_mul halpha.1 (hpLower n hn)
          (by positivity) (by linarith [halpha.1])
  · rw [normalizedLogisticProbability]
    calc
      normalizationFactor lam N * rawLogisticProbability lam N n ≤
          ((1 + Real.exp lam) / 2) * (1 / (1 + Real.exp lam)) := by
        exact mul_le_mul halphaEnd hpUpper
          (rawLogisticProbability_nonneg _ _ _) (by linarith [halpha.1])
      _ = 1 / 2 := by field_simp

/-! ## Uniform logarithmic stability -/

/-- A single error controlling both coordinate log-likelihoods. -/
def logPerturbationError (lam : ℝ) (N : ℕ) : ℝ :=
  |Real.log (normalizationFactor lam N)| +
    4 * |normalizationFactor lam N - 1|

theorem tendsto_logPerturbationError {lam : ℝ}
    (hlam : IsUniqueCriticalParameter lam) :
    Tendsto (logPerturbationError lam) atTop (nhds 0) := by
  have halpha := tendsto_normalizationFactor hlam
  have hlog : Tendsto
      (fun N : ℕ ↦ Real.log (normalizationFactor lam N)) atTop (nhds 0) := by
    simpa only [Real.log_one] using halpha.log one_ne_zero
  have hdiff : Tendsto
      (fun N : ℕ ↦ normalizationFactor lam N - 1) atTop (nhds 0) := by
    have := halpha.sub (tendsto_const_nhds (x := (1 : ℝ)))
    simpa only [sub_self] using this
  have h := hlog.abs.add (hdiff.abs.const_mul 4)
  change Tendsto (fun N : ℕ ↦
    |Real.log (normalizationFactor lam N)| +
      4 * |normalizationFactor lam N - 1|) atTop (nhds 0)
  simpa only [abs_zero, mul_zero, add_zero] using h

theorem eventually_logPerturbationError_lt {lam : ℝ}
    (hlam : IsUniqueCriticalParameter lam) {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ N : ℕ in atTop, logPerturbationError lam N < delta :=
  (tendsto_logPerturbationError hlam).eventually (eventually_lt_nhds hdelta)

lemma logPerturbationError_nonneg (lam : ℝ) (N : ℕ) :
    0 ≤ logPerturbationError lam N := by
  unfold logPerturbationError
  exact add_nonneg (abs_nonneg _) (mul_nonneg (by norm_num) (abs_nonneg _))

/-- The selected-coordinate log changes by at most the common error. -/
lemma selected_log_close {lam : ℝ} {N n : ℕ}
    (halpha : 0 < normalizationFactor lam N)
    (hN : 0 < N) (hn : 0 < n) :
    |Real.log (normalizedLogisticProbability lam N n) -
        Real.log (rawLogisticProbability lam N n)| ≤
      logPerturbationError lam N := by
  have hp : 0 < rawLogisticProbability lam N n :=
    rawLogisticProbability_pos hN hn
  rw [normalizedLogisticProbability, Real.log_mul halpha.ne' hp.ne']
  dsimp [logPerturbationError]
  rw [add_sub_cancel_right]
  exact le_add_of_nonneg_right
    (mul_nonneg (by norm_num) (abs_nonneg _))

/-- A positive-logarithm comparison used for the omitted-coordinate error. -/
private lemma abs_log_sub_log_le_four_mul {a b e : ℝ}
    (ha : 1 / 4 ≤ a) (hb : 1 / 4 ≤ b) (hab : |a - b| ≤ e)
    (he : 0 ≤ e) :
    |Real.log a - Real.log b| ≤ 4 * e := by
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hb0 : 0 < b := lt_of_lt_of_le (by norm_num) hb
  have hba : b - a ≤ e := (le_abs_self (b - a)).trans (by
    rw [abs_sub_comm]
    exact hab)
  have hab' : a - b ≤ e := (le_abs_self (a - b)).trans hab
  have hu : Real.log a - Real.log b ≤ 4 * e := by
    rw [← Real.log_div ha0.ne' hb0.ne']
    calc
      Real.log (a / b) ≤ a / b - 1 :=
        Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
      _ = (a - b) / b := by field_simp
      _ ≤ e / (1 / 4) := by
        exact div_le_div₀ he hab' (by norm_num) hb
      _ = 4 * e := by ring
  have hl : -(4 * e) ≤ Real.log a - Real.log b := by
    have hrev : Real.log b - Real.log a ≤ 4 * e := by
      rw [← Real.log_div hb0.ne' ha0.ne']
      calc
        Real.log (b / a) ≤ b / a - 1 :=
          Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
        _ = (b - a) / a := by field_simp
        _ ≤ e / (1 / 4) := by
          exact div_le_div₀ he hba (by norm_num) ha
        _ = 4 * e := by ring
    linarith
  exact abs_le.mpr ⟨hl, hu⟩

/-- The omitted-coordinate log is uniformly stable whenever the common
multiplier lies in `[1/2,3/2]`. -/
lemma omitted_log_close {lam : ℝ} (hlam : 0 < lam) {N n : ℕ}
    (hN : 0 < N) (hn : 0 < n)
    (_halphaLower : 1 / 2 ≤ normalizationFactor lam N)
    (halphaUpper : normalizationFactor lam N ≤ 3 / 2) :
    |Real.log (1 - normalizedLogisticProbability lam N n) -
        Real.log (1 - rawLogisticProbability lam N n)| ≤
      logPerturbationError lam N := by
  let p := rawLogisticProbability lam N n
  let alpha := normalizationFactor lam N
  have hp0 : 0 ≤ p := rawLogisticProbability_nonneg _ _ _
  have hphalf : p ≤ 1 / 2 := rawLogisticProbability_le_half hlam hN hn
  have ha : 1 / 4 ≤ 1 - alpha * p := by
    dsimp [alpha, p]
    nlinarith [mul_le_mul halphaUpper hphalf hp0 (by norm_num : (0 : ℝ) ≤ 3 / 2)]
  have hb : 1 / 4 ≤ 1 - p := by linarith
  have hdiff : |(1 - alpha * p) - (1 - p)| ≤ |alpha - 1| := by
    rw [show (1 - alpha * p) - (1 - p) = -(alpha - 1) * p by ring,
      abs_mul, abs_neg, abs_of_nonneg hp0]
    exact mul_le_of_le_one_right (abs_nonneg _) (hphalf.trans (by norm_num))
  have hlog := abs_log_sub_log_le_four_mul ha hb hdiff (abs_nonneg _)
  change |Real.log (1 - alpha * p) - Real.log (1 - p)| ≤ _
  exact hlog.trans (le_add_of_nonneg_left (abs_nonneg _))

/-- Uniform, simultaneous selected/omitted log-likelihood control on the
entire source good set. -/
theorem eventually_uniform_log_close {lam : ℝ}
    (hlam : IsUniqueCriticalParameter lam) :
    ∀ᶠ N : ℕ in atTop, ∀ n ∈ goodSet N,
      |Real.log (normalizedLogisticProbability lam N n) -
          Real.log (rawLogisticProbability lam N n)| ≤
            logPerturbationError lam N ∧
      |Real.log (1 - normalizedLogisticProbability lam N n) -
          Real.log (1 - rawLogisticProbability lam N n)| ≤
            logPerturbationError lam N := by
  filter_upwards [eventually_normalizationFactor_bounds hlam,
    eventually_pos_scales, eventually_real_scales_ge_two] with
      N halpha hscales hreal n hn
  rcases hscales with ⟨hNreal, hlog, hLL, ht⟩
  have hN : 0 < N := by exact_mod_cast hNreal
  have hgood := mem_goodDenominators.mp hn
  have hnpos : 0 < n := by
    have hMhalf := half_le_floor hreal.2.2
    have hMone : (1 : ℝ) ≤ M N :=
      (show (1 : ℝ) ≤ MReal N / 2 by linarith [hreal.2.2]).trans hMhalf
    exact_mod_cast lt_of_lt_of_le (zero_lt_one : (0 : ℝ) < 1)
      (hMone.trans (by exact_mod_cast hgood.1 : (M N : ℝ) ≤ n))
  have halphapos : 0 < normalizationFactor lam N := by linarith [halpha.1]
  exact ⟨selected_log_close halphapos hN hnpos,
    omitted_log_close (criticalParameter_pos hlam) hN hnpos halpha.1 halpha.2⟩

/-- A convenient strict probability-range corollary for product-measure
normalization and information identities. -/
theorem eventually_normalized_probability_mem_Ioo {lam : ℝ}
    (hlam : IsUniqueCriticalParameter lam) :
    ∀ᶠ N : ℕ in atTop, ∀ n ∈ goodSet N,
      0 < normalizedLogisticProbability lam N n ∧
        normalizedLogisticProbability lam N n < 1 := by
  filter_upwards [eventually_normalized_probability_bounds hlam,
    eventually_pos_scales] with N hb hscales n hn
  have hLLpos : 0 < logLogScale N := zero_lt_one.trans hscales.2.2.1
  constructor
  · exact (one_div_pos.mpr hLLpos).trans_le (hb n hn).1
  · exact (hb n hn).2.trans_lt (by norm_num)

end

end Erdos297.LogisticNormalization

#print axioms Erdos297.LogisticNormalization.tendsto_rawReciprocalMean
#print axioms Erdos297.LogisticNormalization.eventually_normalized_probability_bounds
#print axioms Erdos297.LogisticNormalization.eventually_uniform_log_close
