import Arxiv.Arxiv2411_18291.FiniteModularQuarterGenerators

/-! # Sparse modular generators in a supplied typical graph at n0 -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_good_modular_generators_paper_threshold {q r n h N : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hN : 0 < N) (hNb : N ≤ (r + 1).factorial * q.choose (r + 1))
    (hqh : q.choose (r + 1) ≤ h) (K : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1))) :
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
  obtain ⟨C, hθ, hcard, hsat, hbad, hcount⟩ :=
    exists_good_modular_generators_quarter_paper_threshold hqr hn hN hNb hqh K hT hd
  have hε0 := Real.rpow_nonneg (Nat.cast_nonneg n) (-(paperAlpha q (r + 1) / 10))
  have hεle : (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) / 4 ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) := by linarith only [hε0]
  refine ⟨C, hθ, hcard, ?_, ?_, ?_⟩
  · exact hsat.trans (mul_le_mul_of_nonneg_right hεle (Nat.cast_nonneg _))
  · exact hbad.trans (mul_le_mul_of_nonneg_right hεle (Nat.cast_nonneg _))
  · intro e he
    exact (hcount e he).trans_le (mul_le_mul_of_nonneg_right hεle
      (cliqueMainTerm_nonneg (Nat.cast_nonneg _) (density_nonneg K) _ _ _))

end Arxiv2411_18291
