import Arxiv.Arxiv2411_18291.FiniteModularGenerators
import Arxiv.Arxiv2411_18291.FiniteReferenceModularGenerators
import Arxiv.Arxiv2411_18291.FiniteTypicalityProbability

/-! # Corrected probability for sparse modular generators at n0

The sampled graph itself admits the generating data. Both the original
observed-density interface and the source's reference-density binomial
normalization are proved, with corrected failure below `exp(-n^(1/10))`.
-/

open MeasureTheory

noncomputable section

namespace Arxiv2411_18291

theorem modular_generators_paper_whp_corrected {q r n h N : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hN : 0 < N) (hNb : N ≤ (r + 1).factorial * q.choose (r + 1))
    (hqh : q.choose (r + 1) ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (p : unitInterval) (hp : (p : ℝ) = (n : ℝ) ^ (-paperAlpha q (r + 1))) :
    1 - Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) <
      (BernoulliSubset.probability (Block (Fin n) (r + 1)) p).real
        {ω | let K := sampleGraph ω
          IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h ∧
          |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
            (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)) ∧
          ∃ C : ModularGeneratingData K (cliqueFamily K q) N,
            IsCliqueFamilyBounded r C.generators
              (2 ^ q * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))) ∧
            C.generators.card ≤ N * K.card ∧
            (C.saturated.card : ℝ) ≤
              (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * (cliqueFamily K q).card ∧
            ((K \ C.good).card : ℝ) ≤
              (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card ∧
            ∀ e ∈ C.good,
              |((((cliqueFamily K q) \ C.saturated).filter fun Q => e.val ⊆ Q.val).card : ℝ) -
                cliqueMainTerm n (density K) q (r + 1) (r + 1)| <
                (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) *
                  cliqueMainTerm n (density K) q (r + 1) (r + 1)} := by
  have hh : 1 ≤ h := (Nat.succ_le_iff.mpr (Nat.choose_pos hqr.le)).trans hqh
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hα : paperAlpha q (r + 1) ≤ 1 / (2 * h : ℝ) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hh := paperAlpha_mul_configuration_le hqr hH
    nlinarith only [hh]
  have hpLower : (n : ℝ) ^ (-(1 / (2 * h : ℝ))) ≤ p := by
    rw [hp]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg hα)
  have hprob := typical_paper_whp_corrected_paper_threshold hqr hn hh hH p hpLower
  apply hprob.trans_le
  refine measureReal_mono ?_ (by finiteness)
  intro ω hω
  change |density (sampleGraph ω) - (p : ℝ)| ≤ (n : ℝ) ^ (-(1 / 10 : ℝ)) * p ∧
    IsTypical (sampleGraph ω) ((n : ℝ) ^ (-(1 / 10 : ℝ))) h at hω
  rw [hp] at hω
  exact ⟨hω.2, hω.1,
    exists_good_modular_generators_paper_threshold hqr hn hN hNb hqh _ hω.2 hω.1⟩

theorem reference_modular_generators_whp_of_margin {q r n h N : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hN : 0 < N) (hNb : (256 * q.choose (r + 1) * q.choose r * N : ℝ) ≤
      (n : ℝ) ^ (paperAlpha q (r + 1) / 10))
    (hqh : q.choose (r + 1) ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (p : unitInterval) (hp : (p : ℝ) = (n : ℝ) ^ (-paperAlpha q (r + 1))) :
    1 - Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) <
      (BernoulliSubset.probability (Block (Fin n) (r + 1)) p).real
        {ω | let K := sampleGraph ω
          IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h ∧
          |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
            (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)) ∧
          ∃ C : ModularGeneratingData K (cliqueFamily K q) N,
            IsCliqueFamilyBounded r C.generators
              (2 ^ q * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))) ∧
            C.generators.card ≤ N * K.card ∧
            (C.saturated.card : ℝ) <
              (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10) -
                (q.choose (r + 1) : ℝ) * paperAlpha q (r + 1)) * (n.choose q : ℝ) ∧
            ((K \ C.good).card : ℝ) <
              (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card ∧
            ∀ e ∈ C.good,
              |((((cliqueFamily K q) \ C.saturated).filter fun Q => e.val ⊆ Q.val).card : ℝ) -
                (n : ℝ) ^ (paperAlpha q (r + 1) -
                  (q.choose (r + 1) : ℝ) * paperAlpha q (r + 1)) *
                    (n.choose (q - (r + 1)) : ℝ)| <
                (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) *
                  ((n : ℝ) ^ (paperAlpha q (r + 1) -
                    (q.choose (r + 1) : ℝ) * paperAlpha q (r + 1)) *
                      (n.choose (q - (r + 1)) : ℝ))} := by
  have hh : 1 ≤ h := (Nat.succ_le_iff.mpr (Nat.choose_pos hqr.le)).trans hqh
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hα : paperAlpha q (r + 1) ≤ 1 / (2 * h : ℝ) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hh := paperAlpha_mul_configuration_le hqr hH
    nlinarith only [hh]
  have hpLower : (n : ℝ) ^ (-(1 / (2 * h : ℝ))) ≤ p := by
    rw [hp]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg hα)
  have hprob := typical_paper_whp_corrected_paper_threshold hqr hn hh hH p hpLower
  apply hprob.trans_le
  refine measureReal_mono ?_ (by finiteness)
  intro ω hω
  change |density (sampleGraph ω) - (p : ℝ)| ≤ (n : ℝ) ^ (-(1 / 10 : ℝ)) * p ∧
    IsTypical (sampleGraph ω) ((n : ℝ) ^ (-(1 / 10 : ℝ))) h at hω
  rw [hp] at hω
  exact ⟨hω.2, hω.1,
    exists_reference_modular_generators_of_margin hqr hn hN hNb hqh _ hω.2 hω.1⟩

theorem reference_modular_generators_paper_whp_corrected {q r n h N : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hN : 0 < N) (hNb : N ≤ (r + 1).factorial * q.choose (r + 1))
    (hqh : q.choose (r + 1) ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (p : unitInterval) (hp : (p : ℝ) = (n : ℝ) ^ (-paperAlpha q (r + 1))) :
    1 - Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) <
      (BernoulliSubset.probability (Block (Fin n) (r + 1)) p).real
        {ω | let K := sampleGraph ω
          IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h ∧
          |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
            (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)) ∧
          ∃ C : ModularGeneratingData K (cliqueFamily K q) N,
            IsCliqueFamilyBounded r C.generators
              (2 ^ q * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))) ∧
            C.generators.card ≤ N * K.card ∧
            (C.saturated.card : ℝ) <
              (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10) -
                (q.choose (r + 1) : ℝ) * paperAlpha q (r + 1)) * (n.choose q : ℝ) ∧
            ((K \ C.good).card : ℝ) <
              (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card ∧
            ∀ e ∈ C.good,
              |((((cliqueFamily K q) \ C.saturated).filter fun Q => e.val ⊆ Q.val).card : ℝ) -
                (n : ℝ) ^ (paperAlpha q (r + 1) -
                  (q.choose (r + 1) : ℝ) * paperAlpha q (r + 1)) *
                    (n.choose (q - (r + 1)) : ℝ)| <
                (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) *
                  ((n : ℝ) ^ (paperAlpha q (r + 1) -
                    (q.choose (r + 1) : ℝ) * paperAlpha q (r + 1)) *
                      (n.choose (q - (r + 1)) : ℝ))} := by
  exact reference_modular_generators_whp_of_margin hqr hn hN
    (generator_modulus_margin_paper_threshold hqr hn hNb) hqh hH p hp

end Arxiv2411_18291
