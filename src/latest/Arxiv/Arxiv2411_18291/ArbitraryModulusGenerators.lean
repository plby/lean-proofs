import Arxiv.Arxiv2411_18291.ModulusDependentThreshold
import Arxiv.Arxiv2411_18291.ModularGeneratorsProbability

/-!
# Sparse modular generators for every positive modulus

All three source conclusions use the original reference-density binomial
normalization. The actual random host has the corrected probability bound
at an explicit modulus-dependent threshold; no upper bound on N is assumed.
-/

open MeasureTheory

noncomputable section

namespace Arxiv2411_18291

theorem reference_modular_generators_whp_modulus_threshold {q r n h N : ℕ}
    (hqr : r + 1 < q) (hn : correctedModularGeneratorThreshold q r N ≤ n)
    (hN : 0 < N)
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
  exact reference_modular_generators_whp_of_margin hqr
    ((paperThreshold_le_modularGeneratorThreshold q r N).trans hn) hN
    (modular_generator_margin_of_threshold hqr hn) hqh hH p hp

theorem exists_sparse_reference_modular_generators_modulus_threshold {q r n h N : ℕ}
    (hqr : r + 1 < q) (hn : correctedModularGeneratorThreshold q r N ≤ n)
    (hN : 0 < N)
    (hqh : q.choose (r + 1) ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2) :
    ∃ K : Hypergraph (Fin n) (r + 1),
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
                  (n.choose (q - (r + 1)) : ℝ)) := by
  have hnPaper := (paperThreshold_le_modularGeneratorThreshold q r N).trans hn
  have hnNat : 1 ≤ n := (paperSizeThreshold_one_lt hqr).le.trans hnPaper
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnNat
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnNat
  let p : unitInterval := ⟨(n : ℝ) ^ (-paperAlpha q (r + 1)),
    Real.rpow_nonneg hn0.le _,
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (neg_nonpos.mpr (paperAlpha_pos hqr).le)⟩
  have hprob := reference_modular_generators_whp_modulus_threshold hqr hn hN hqh hH p rfl
  have hpos : 0 < 1 - Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) := by
    apply sub_pos.mpr
    exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos (Real.rpow_pos_of_pos hn0 _))
  obtain ⟨ω, hω⟩ := MeasureTheory.nonempty_of_measureReal_ne_zero
    (ne_of_gt (hpos.trans hprob))
  exact ⟨sampleGraph ω, hω⟩

end Arxiv2411_18291
