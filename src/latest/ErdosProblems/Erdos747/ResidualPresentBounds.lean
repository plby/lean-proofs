import ErdosProblems.Erdos747.ResidualGoodBounds

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Density-independent entropy bounds in residual dimensions -/

def aggregatePresentTolerance (k : ℕ) (C g q eta B : ℝ) : ℝ :=
  normalizedSpreadTolerance k C (normalizedEntropyEnvelope C g) q eta B

lemma aggregatePresentTolerance_nonneg (k : ℕ) (C g q eta B : ℝ) :
    0 ≤ aggregatePresentTolerance k C g q eta B := Real.sqrt_nonneg _

lemma aggregatePresentTolerance_pos (k : ℕ) (C g q eta B : ℝ)
    (hk : 0 < k) (hC : 0 ≤ C) (hq : 0 ≤ q) (heta : 0 ≤ eta) (hB : 0 ≤ B) :
    0 < aggregatePresentTolerance k C g q eta B :=
  normalizedSpreadTolerance_pos k C _ q eta B hk hC hq heta hB

lemma kahnAggregateInsertionGood_presentWeightSpread_of_relativeCodegree
    {k M cap : ℕ} {C g q eta B : ℝ} {H : Finset (Edge k)}
    (hk : 3 ≤ k) (hM : 0 < M) (hcap : 0 < cap)
    (hC : 0 ≤ C) (hg : 0 < g) (hq : 0 ≤ q) (heta : 0 ≤ eta) (hB : 0 ≤ B)
    (hR : 1 < entropyRatioEnvelope g)
    (hrelative : (cap : ℝ) / ((M : ℝ) / k) ≤ g)
    (hgood : KahnAggregateInsertionGood k M cap C q eta B H) :
    PresentWeightSpread H (aggregatePresentTolerance k C g q eta B)
      (aggregatePresentTolerance k C g q eta B) := by
  have hratio := entropyRatioEnvelope_le_layerRatio k M cap g (by omega) hM hcap hg hrelative
  exact kahnAggregateInsertionGood_presentWeightSpread_normalized
    (sigma := Real.sqrt g) hk hM hcap hC (normalizedEntropyEnvelope_nonneg C g hC hR)
    (Real.sqrt_pos.mpr hg) hq heta hB (hR.trans_le hratio)
    (entropy_genericity_budget_le_normalized_envelope k M cap C g (by omega) hM hcap
      hC hg hR hrelative) hgood

lemma normalizedLocalSpreadError_tendsto_zero_along
    (k : ℕ → ℕ) (C e : ℕ → ℝ) (hk : Tendsto k atTop atTop)
    (hC : Tendsto C atTop (𝓝 0)) (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n ↦ normalizedLocalSpreadError (k n) (C n) (e n)) atTop (𝓝 0) := by
  have hcast : Tendsto (fun n ↦ (k n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hk
  have hinv : Tendsto (fun n : ℕ ↦ (Real.sqrt (k n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hcast)
  have hroot := ((he.sqrt.mul_const (Real.sqrt 3)).sqrt).mul_const (Real.sqrt 3)
  have hlim := (((hC.const_mul 3).add (hinv.const_mul 12)).add (hroot.const_mul 10)).const_mul 12
  simpa only [normalizedLocalSpreadError, div_eq_mul_inv, zero_mul, mul_zero,
    add_zero, Real.sqrt_zero] using hlim.sqrt

lemma aggregatePresentTolerance_tendsto_zero_along
    (k : ℕ → ℕ) (C g q eta : ℕ → ℝ) (B : ℝ)
    (hk : Tendsto k atTop atTop) (hC : Tendsto C atTop (𝓝 0))
    (hg : Tendsto g atTop (𝓝 0)) (hgpos : ∀ᶠ n in atTop, 0 < g n)
    (hq : Tendsto q atTop (𝓝 0)) (heta : Tendsto eta atTop (𝓝 0)) :
    Tendsto (fun n ↦ aggregatePresentTolerance (k n) (C n) (g n) (q n) (eta n) B)
      atTop (𝓝 0) := by
  have he := normalizedEntropyEnvelope_tendsto_zero C g hC hg hgpos
  have hlocal := normalizedLocalSpreadError_tendsto_zero_along k C _ hk hC he
  have hlim := ((hlocal.div_const 3).add hq).add (heta.mul_const (1 + B))
  simpa only [aggregatePresentTolerance, normalizedSpreadTolerance, zero_div,
    zero_mul, add_zero, Real.sqrt_zero] using hlim.sqrt

lemma nat_sub_const_tendsto_atTop (j : ℕ) :
    Tendsto (fun n : ℕ ↦ n - j) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (b + j)] with n hn
  omega

lemma eventually_aggregatePresentWeightSpread_along
    (k : ℕ → ℕ) (C g q eta : ℕ → ℝ) (B : ℝ)
    (hk : Tendsto k atTop atTop) (hC0 : ∀ᶠ n in atTop, 0 ≤ C n)
    (hg : Tendsto g atTop (𝓝 0)) (hgpos : ∀ᶠ n in atTop, 0 < g n)
    (hq0 : ∀ᶠ n in atTop, 0 ≤ q n) (heta0 : ∀ᶠ n in atTop, 0 ≤ eta n)
    (hB : 0 ≤ B) :
    ∀ᶠ n in atTop, ∀ M cap : ℕ, 0 < M → 0 < cap →
      (cap : ℝ) / ((M : ℝ) / k n) ≤ g n →
      ∀ H, KahnAggregateInsertionGood (k n) M cap (C n) (q n) (eta n) B H →
        PresentWeightSpread H (aggregatePresentTolerance (k n) (C n) (g n) (q n) (eta n) B)
          (aggregatePresentTolerance (k n) (C n) (g n) (q n) (eta n) B) := by
  have hR := entropyRatioEnvelope_tendsto_atTop g hg hgpos
  filter_upwards [hk.eventually_ge_atTop 3, hC0, hgpos, hq0, heta0,
    hR.eventually_ge_atTop 2] with n hkn hCn hgn hqn hetan hRn
  intro M cap hM hcap hrelative H hgood
  exact kahnAggregateInsertionGood_presentWeightSpread_of_relativeCodegree
    hkn hM hcap hCn hgn hqn hetan hB (by linarith) hrelative hgood

end

end Erdos747
