import Arxiv.Arxiv2411_18291.ModularGeneratorsProbability
import Arxiv.Arxiv2411_18291.FiniteTypicalHost

/-! # Constructing the typical host and its sparse modular generators at n0 -/

noncomputable section

namespace Arxiv2411_18291

theorem exists_sparse_modular_generators_paper_threshold {q r n h N : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hN : 0 < N) (hNb : N ≤ (r + 1).factorial * q.choose (r + 1))
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
        (C.saturated.card : ℝ) ≤
          (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * (cliqueFamily K q).card ∧
        ((K \ C.good).card : ℝ) ≤
          (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card ∧
        ∀ e ∈ C.good,
          |((((cliqueFamily K q) \ C.saturated).filter fun Q => e.val ⊆ Q.val).card : ℝ) -
            cliqueMainTerm n (density K) q (r + 1) (r + 1)| <
            (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) *
              cliqueMainTerm n (density K) q (r + 1) (r + 1) := by
  have hnNat : 1 ≤ n := (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnNat
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnNat
  let p : unitInterval := ⟨(n : ℝ) ^ (-paperAlpha q (r + 1)),
    Real.rpow_nonneg hn0.le _,
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (neg_nonpos.mpr (paperAlpha_pos hqr).le)⟩
  have hprob := modular_generators_paper_whp_corrected hqr hn hN hNb hqh hH p rfl
  have hpos : 0 < 1 - Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) := by
    apply sub_pos.mpr
    exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos (Real.rpow_pos_of_pos hn0 _))
  obtain ⟨ω, hω⟩ := MeasureTheory.nonempty_of_measureReal_ne_zero
    (ne_of_gt (hpos.trans hprob))
  exact ⟨sampleGraph ω, hω⟩

theorem exists_sparse_reference_modular_generators_paper_threshold {q r n h N : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hN : 0 < N) (hNb : N ≤ (r + 1).factorial * q.choose (r + 1))
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
  have hnNat : 1 ≤ n := (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnNat
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnNat
  let p : unitInterval := ⟨(n : ℝ) ^ (-paperAlpha q (r + 1)),
    Real.rpow_nonneg hn0.le _,
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (neg_nonpos.mpr (paperAlpha_pos hqr).le)⟩
  have hprob := reference_modular_generators_paper_whp_corrected hqr hn hN hNb hqh hH p rfl
  have hpos : 0 < 1 - Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) := by
    apply sub_pos.mpr
    exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos (Real.rpow_pos_of_pos hn0 _))
  obtain ⟨ω, hω⟩ := MeasureTheory.nonempty_of_measureReal_ne_zero
    (ne_of_gt (hpos.trans hprob))
  exact ⟨sampleGraph ω, hω⟩

end Arxiv2411_18291
