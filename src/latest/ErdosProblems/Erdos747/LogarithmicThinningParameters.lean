import ErdosProblems.Erdos747.AggregateGlobalBounds

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

def logarithmicThinningSize (nu : ℝ) (n : ℕ) : ℕ := ⌈nu * Real.log ((3 * n : ℕ) : ℝ)⌉₊

def halfLogMean (n : ℕ) : ℝ := Real.log ((3 * n : ℕ) : ℝ) / 2

def logarithmicThinningMultiplier (nu : ℝ) : ℝ := 2 * (nu + 1)

lemma halfLogMean_tendsto_atTop : Tendsto halfLogMean atTop atTop := by
  exact log_vertexCount_tendsto_atTop.atTop_div_const (by norm_num)

lemma logarithmicThinningMultiplier_pos (nu : ℝ) (hnu : 0 ≤ nu) :
    0 < logarithmicThinningMultiplier nu := by unfold logarithmicThinningMultiplier; positivity

lemma eventually_logarithmicThinningSize_bounds (nu : ℝ) (hnu : 0 < nu) :
    ∀ᶠ n in atTop, 2 ≤ logarithmicThinningSize nu n ∧
      (logarithmicThinningSize nu n : ℝ) ≤ logarithmicThinningMultiplier nu * halfLogMean n := by
  have hprod := log_vertexCount_tendsto_atTop.const_mul_atTop hnu
  filter_upwards [hprod.eventually_ge_atTop 2, log_vertexCount_tendsto_atTop.eventually_ge_atTop 1]
    with n hlarge hlog
  have hlo : nu * Real.log ((3 * n : ℕ) : ℝ) ≤ logarithmicThinningSize nu n := Nat.le_ceil _
  have hhi : (logarithmicThinningSize nu n : ℝ) < nu * Real.log ((3 * n : ℕ) : ℝ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  constructor
  · exact_mod_cast hlarge.trans hlo
  · unfold logarithmicThinningMultiplier halfLogMean
    nlinarith only [hhi, hlog]

lemma logarithmicThinningSize_sq_div_tendsto_zero (nu : ℝ) (hnu : 0 ≤ nu) :
    Tendsto (fun n ↦ (logarithmicThinningSize nu n : ℝ)^2 / n) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ ↦ (2 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hbound := (tendsto_sq_log_three_mul_div.const_mul (2 * nu^2)).add hinv
  norm_num only [mul_zero, add_zero] at hbound
  apply squeeze_zero' (Eventually.of_forall fun n ↦ by positivity) _ hbound
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log ((3 * n : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 3 * n by omega))
  have hceil : (logarithmicThinningSize nu n : ℝ) ≤ nu * Real.log ((3 * n : ℕ) : ℝ) + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hsq := (sq_le_sq₀ (Nat.cast_nonneg _) (by positivity : 0 ≤ nu * Real.log ((3 * n : ℕ) : ℝ) + 1)).mpr hceil
  have hnum : (logarithmicThinningSize nu n : ℝ)^2 ≤
      2 * nu^2 * (Real.log ((3 * n : ℕ) : ℝ))^2 + 2 := by
    nlinarith only [hsq, sq_nonneg (nu * Real.log ((3 * n : ℕ) : ℝ) - 1)]
  calc
    _ ≤ (2 * nu^2 * (Real.log ((3 * n : ℕ) : ℝ))^2 + 2) / n :=
      div_le_div_of_nonneg_right hnum hnR.le
    _ = _ := by ring

lemma eventually_logarithmicThinning_finite_budgets (nu zeta : ℝ)
    (hnu : 0 < nu) (hzeta : 0 < zeta) :
    ∀ᶠ n in atTop, 2 ≤ logarithmicThinningSize nu n ∧
      (logarithmicThinningSize nu n : ℝ) ≤ logarithmicThinningMultiplier nu * halfLogMean n ∧
      logarithmicThinningSize nu n * logarithmicThinningSize nu n ≤ thinningBlockSize (allEdges n).card zeta ∧
      ∀ M : ℕ, halfLogMean n ≤ (M : ℝ) / n →
        4 * logarithmicThinningSize nu n * logarithmicThinningSize nu n ≤ M := by
  have hratio := logarithmicThinningSize_sq_div_tendsto_zero nu hnu.le
  have hsmall1 := (tendsto_order.mp hratio).2 (1 / 4) (by norm_num : (0 : ℝ) < 1 / 4)
  have hsmall2 := (tendsto_order.mp hratio).2 (zeta / 16) (by positivity : (0 : ℝ) < zeta / 16)
  have hzN : Tendsto (fun n : ℕ ↦ zeta * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hzeta
  filter_upwards [eventually_logarithmicThinningSize_bounds nu hnu, hsmall1, hsmall2,
    hzN.eventually_ge_atTop 16, halfLogMean_tendsto_atTop.eventually_ge_atTop 1,
    eventually_ge_atTop 1] with n hsize hs1 hs2 hzlarge hmean hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hK : (n : ℝ) ≤ (allEdges n).card := by
    have hnat := Finset.card_le_card (canonicalMatching_subset_allEdges n)
    rw [canonicalMatching_card] at hnat
    exact_mod_cast hnat
  have hlargeK := hzlarge.trans (mul_le_mul_of_nonneg_left hK hzeta.le)
  have hs1' := (div_lt_iff₀ hnR).mp hs1
  have hs2' := (div_lt_iff₀ hnR).mp hs2
  refine ⟨hsize.1, hsize.2, ?_, ?_⟩
  · have hd := (thinningBlockSize_bounds (allEdges n).card zeta hzeta.le hlargeK).1
    have hzK := mul_le_mul_of_nonneg_left hK hzeta.le
    have htR : (logarithmicThinningSize nu n : ℝ)^2 ≤ thinningBlockSize (allEdges n).card zeta := by
      nlinarith only [hs2', hd, hzK]
    exact_mod_cast (show (logarithmicThinningSize nu n : ℝ) * logarithmicThinningSize nu n ≤
      thinningBlockSize (allEdges n).card zeta by simpa only [pow_two] using htR)
  · intro M hM
    have hMN : (n : ℝ) ≤ M := by
      have h := (le_div_iff₀ hnR).mp (hmean.trans hM)
      simpa only [one_mul] using h
    have htR : (4 : ℝ) * logarithmicThinningSize nu n * logarithmicThinningSize nu n ≤ M := by
      nlinarith only [hs1', hMN]
    exact_mod_cast htR

lemma logarithmicThinning_tail_le (n : ℕ) (nu zeta : ℝ) (hzeta : 0 ≤ zeta) :
    4 * Real.exp (-((logarithmicThinningSize nu n : ℝ) * zeta) / 1024) ≤
      4 * Real.exp (-(nu * zeta / 1024) * Real.log ((3 * n : ℕ) : ℝ)) := by
  have hlo : nu * Real.log ((3 * n : ℕ) : ℝ) ≤ logarithmicThinningSize nu n := Nat.le_ceil _
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right hlo hzeta
  nlinarith only [h]

end

end Erdos747
