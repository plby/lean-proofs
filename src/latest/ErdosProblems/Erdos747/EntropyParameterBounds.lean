import ErdosProblems.Erdos747.NormalizedPresentSpread

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Density-uniform parameters for the entropy genericity error -/

def entropyRatioEnvelope (g : ℝ) : ℝ := 1 / (6 * Real.sqrt g)

def normalizedEntropyEnvelope (C g : ℝ) : ℝ :=
  3 * Real.sqrt (Real.sqrt g) +
    3 * (C + 14 + Real.log 2) / Real.log (entropyRatioEnvelope g)

lemma entropyRatioEnvelope_tendsto_atTop
    (g : ℕ → ℝ) (hg : Tendsto g atTop (𝓝 0))
    (hgpos : ∀ᶠ n : ℕ in atTop, 0 < g n) :
    Tendsto (fun n ↦ entropyRatioEnvelope (g n)) atTop atTop := by
  have hscaled : Tendsto (fun n ↦ (6 : ℝ) * Real.sqrt (g n)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, mul_zero] using hg.sqrt.const_mul 6
  have hwithin : Tendsto (fun n ↦ (6 : ℝ) * Real.sqrt (g n)) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hscaled, ?_⟩
    filter_upwards [hgpos] with n hn
    change 0 < (6 : ℝ) * Real.sqrt (g n)
    positivity
  simpa only [entropyRatioEnvelope, one_div, Function.comp_def] using
    tendsto_inv_nhdsGT_zero.comp hwithin

lemma normalizedEntropyEnvelope_tendsto_zero
    (C g : ℕ → ℝ) (hC : Tendsto C atTop (𝓝 0))
    (hg : Tendsto g atTop (𝓝 0)) (hgpos : ∀ᶠ n : ℕ in atTop, 0 < g n) :
    Tendsto (fun n ↦ normalizedEntropyEnvelope (C n) (g n)) atTop (𝓝 0) := by
  have hroot := hg.sqrt.sqrt.const_mul 3
  have hnum := ((hC.add_const 14).add_const (Real.log 2)).const_mul 3
  have hlog := Real.tendsto_log_atTop.comp (entropyRatioEnvelope_tendsto_atTop g hg hgpos)
  have hquot := hnum.div_atTop hlog
  simpa only [normalizedEntropyEnvelope, Real.sqrt_zero, mul_zero, add_zero,
    Function.comp_def] using hroot.add hquot

lemma normalizedEntropyEnvelope_nonneg (C g : ℝ)
    (hC : 0 ≤ C) (hR : 1 < entropyRatioEnvelope g) :
    0 ≤ normalizedEntropyEnvelope C g := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogR : 0 < Real.log (entropyRatioEnvelope g) := Real.log_pos hR
  unfold normalizedEntropyEnvelope
  positivity

lemma entropyRatioEnvelope_le_layerRatio
    (n M cap : ℕ) (g : ℝ) (hn : 0 < n) (hM : 0 < M) (hcap : 0 < cap)
    (hg : 0 < g) (hrelative : (cap : ℝ) / ((M : ℝ) / n) ≤ g) :
    entropyRatioEnvelope g ≤ ((3 * M : ℕ) : ℝ) * Real.sqrt g /
      ((18 * n * cap : ℕ) : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmean : 0 < (M : ℝ) / n := by positivity
  have hcapMean := (div_le_iff₀ hmean).mp hrelative
  have hcapN : (cap : ℝ) * n ≤ g * M := by
    have h := mul_le_mul_of_nonneg_right hcapMean hnR.le
    simpa only [mul_assoc, div_mul_cancel₀ _ hnR.ne'] using h
  unfold entropyRatioEnvelope
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 6 * Real.sqrt g)
    (by positivity : (0 : ℝ) < ((18 * n * cap : ℕ) : ℝ))).mpr
  norm_num only [Nat.cast_mul, Nat.cast_ofNat, one_mul]
  have hsqM := congrArg (fun z : ℝ ↦ (M : ℝ) * z) (Real.sq_sqrt hg.le)
  nlinarith

lemma entropy_genericity_budget_le_normalized_envelope
    (n M cap : ℕ) (C g : ℝ) (hn : 0 < n) (hM : 0 < M) (hcap : 0 < cap)
    (hC : 0 ≤ C) (hg : 0 < g) (hR : 1 < entropyRatioEnvelope g)
    (hrelative : (cap : ℝ) / ((M : ℝ) / n) ≤ g) :
    (3 * n : ℝ) * Real.sqrt (Real.sqrt g) +
      (3 * n : ℝ) * (C + 14 + Real.log 2) /
        Real.log (((3 * M : ℕ) : ℝ) * Real.sqrt g / ((18 * n * cap : ℕ) : ℝ)) ≤
      normalizedEntropyEnvelope C g * n := by
  have hratio := entropyRatioEnvelope_le_layerRatio n M cap g hn hM hcap hg hrelative
  have hlog := Real.log_le_log (lt_trans zero_lt_one hR) hratio
  have hlogR := Real.log_pos hR
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hnum : 0 ≤ (3 * n : ℝ) * (C + 14 + Real.log 2) := by positivity
  calc
    _ ≤ (3 * n : ℝ) * Real.sqrt (Real.sqrt g) +
        (3 * n : ℝ) * (C + 14 + Real.log 2) / Real.log (entropyRatioEnvelope g) :=
      add_le_add le_rfl (div_le_div_of_nonneg_left hnum hlogR hlog)
    _ = _ := by unfold normalizedEntropyEnvelope; ring

lemma eventually_codegreeRelativeError_pos :
    ∀ᶠ n : ℕ in atTop, 0 < codegreeRelativeError n := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hlog : 0 < Real.log ((3 * n : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < 3 * n by omega))
  have htol := codegreeRelativeTolerance_nonneg n
  unfold codegreeRelativeError
  positivity

def standardPresentSpreadTolerance (n : ℕ) (C : ℝ) : ℝ :=
  normalizedSpreadTolerance n C (normalizedEntropyEnvelope C (codegreeRelativeError n))
    (aggregateDegreeTolerance n) (aggregateDegreeTolerance n) 32

lemma standardPresentSpreadTolerance_tendsto_zero
    (C : ℕ → ℝ) (hC : Tendsto C atTop (𝓝 0)) :
    Tendsto (fun n ↦ standardPresentSpreadTolerance n (C n)) atTop (𝓝 0) := by
  exact normalizedSpreadTolerance_tendsto_zero C
    (fun n ↦ normalizedEntropyEnvelope (C n) (codegreeRelativeError n))
    aggregateDegreeTolerance aggregateDegreeTolerance 32 hC
    (normalizedEntropyEnvelope_tendsto_zero C codegreeRelativeError hC
      codegreeRelativeError_tendsto_zero eventually_codegreeRelativeError_pos)
    aggregateDegreeTolerance_tendsto_zero aggregateDegreeTolerance_tendsto_zero

lemma eventually_upperLayer_log_mean_ge (ε R : ℝ) (hε : 0 ≤ ε) :
    ∀ᶠ n : ℕ in atTop, ∀ M : ℕ, upperEdgeCount ε n ≤ M →
      R ≤ Real.log ((M : ℝ) / n) := by
  have hthree : Tendsto (fun n : ℕ ↦ ((3 * n : ℕ) : ℝ)) atTop atTop := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hloglog := Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hthree)
  filter_upwards [hloglog.eventually_ge_atTop R, eventually_ge_atTop 1] with n hR hn
  intro M hM
  have hlogpos : 0 < Real.log ((3 * n : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < 3 * n by omega))
  have hmean : Real.log ((3 * n : ℕ) : ℝ) ≤ (M : ℝ) / n :=
    (upperEdgeCount_mean_ge ε hε n (by omega)).trans
      (div_le_div_of_nonneg_right (by exact_mod_cast hM) (by positivity))
  exact hR.trans (Real.log_le_log hlogpos hmean)

/-- Present-edge spreading follows uniformly over all supercritical
layers from the explicit pathwise base and any vanishing count error. -/
lemma eventually_standardAggregateLayer_presentWeightSpread
    (ε a : ℝ) (C : ℕ → ℝ) (hε : 0 ≤ ε)
    (hC : Tendsto C atTop (𝓝 0)) (hC0 : ∀ᶠ n in atTop, 0 ≤ C n) :
    ∀ᶠ n : ℕ in atTop, ∀ M : ℕ, upperEdgeCount ε n ≤ M →
      ∀ H ∈ sample n M, StandardAggregateLayerRegular n M a H →
        KahnCountLower H (C n) →
          PresentWeightSpread H (standardPresentSpreadTolerance n (C n))
            (standardPresentSpreadTolerance n (C n)) := by
  have hRatio := entropyRatioEnvelope_tendsto_atTop codegreeRelativeError
    codegreeRelativeError_tendsto_zero eventually_codegreeRelativeError_pos
  have hCsmall := (tendsto_order.1 hC).2 1 (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hC0, hCsmall, eventually_codegreeRelativeError_pos,
    hRatio.eventually_ge_atTop 2, eventually_upperLayer_log_mean_ge ε 4 hε,
    eventually_ge_atTop 3] with n hC0n hCsmalln hg hR hmeanall hn
  intro M hMlower H hHs hregular hcount
  have hlogmean := hmeanall M hMlower
  have hM0 : 0 < M := by
    by_contra hbad
    have hz : M = 0 := by omega
    simp only [hz, Nat.cast_zero, zero_div, Real.log_zero] at hlogmean
    linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpositive : 0 < (n : ℝ) * Real.log ((M : ℝ) / n) -
      2 * n - (C n) * n := by
    have hfactor : 0 < Real.log ((M : ℝ) / n) - 2 - C n := by linarith
    nlinarith [mul_pos hnR hfactor]
  have hGood := kahnAggregateInsertionGood_of_aggregateLayerRegular hHs hregular hpositive hcount
  have htol : 0 < codegreeRelativeTolerance n := by
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos
      (by exact_mod_cast (show 1 < n by omega))
    unfold codegreeRelativeTolerance
    positivity
  have hcap : 0 < relativeCodegreeCap n M (codegreeRelativeTolerance n) := by
    have hval : 0 < codegreeRelativeTolerance n * ((M : ℝ) / n) := by positivity
    have hceil := hval.trans_le (Nat.le_ceil (codegreeRelativeTolerance n * ((M : ℝ) / n)))
    exact_mod_cast hceil
  have hrelative := relativeCodegreeCap_ratio_le_error ε hε n M (by omega) hMlower
  have hR1 : 1 < entropyRatioEnvelope (codegreeRelativeError n) := by linarith
  have hratio := entropyRatioEnvelope_le_layerRatio n M
    (relativeCodegreeCap n M (codegreeRelativeTolerance n)) (codegreeRelativeError n)
    (by omega) hM0 hcap hg hrelative
  exact kahnAggregateInsertionGood_presentWeightSpread_normalized
    (sigma := Real.sqrt (codegreeRelativeError n)) hn hM0 hcap hC0n
    (normalizedEntropyEnvelope_nonneg (C n) (codegreeRelativeError n) hC0n hR1)
    (Real.sqrt_pos.mpr hg) (aggregateDegreeTolerance_nonneg n)
    (aggregateDegreeTolerance_nonneg n) (by norm_num) (hR1.trans_le hratio)
    (entropy_genericity_budget_le_normalized_envelope n M
      (relativeCodegreeCap n M (codegreeRelativeTolerance n)) (C n) (codegreeRelativeError n)
      (by omega) hM0 hcap hC0n hg hR1 hrelative) hGood

end

end Erdos747
