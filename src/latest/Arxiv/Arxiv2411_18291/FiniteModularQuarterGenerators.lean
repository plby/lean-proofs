import Arxiv.Arxiv2411_18291.FiniteModularHostNumerics
import Arxiv.Arxiv2411_18291.FiniteModularErrorBudget
import Arxiv.Arxiv2411_18291.GoodGeneratorCriterion

/-! # Modular generators with a quarter of the final relative-error allowance -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_good_modular_generators_quarter_of_margin {q r n h N : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hN : 0 < N) (hNb : (256 * q.choose (r + 1) * q.choose r * N : ℝ) ≤
      (n : ℝ) ^ (paperAlpha q (r + 1) / 10))
    (hqh : q.choose (r + 1) ≤ h) (K : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1))) :
    ∃ C : ModularGeneratingData K (cliqueFamily K q) N,
      IsCliqueFamilyBounded r C.generators
        (2 ^ q * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))) ∧
      C.generators.card ≤ N * K.card ∧
      (C.saturated.card : ℝ) ≤
        ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) / 4) * (cliqueFamily K q).card ∧
      ((K \ C.good).card : ℝ) ≤
        ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) / 4) * K.card ∧
      ∀ e ∈ C.good,
        |((((cliqueFamily K q) \ C.saturated).filter fun Q => e.val ⊆ Q.val).card : ℝ) -
          cliqueMainTerm n (density K) q (r + 1) (r + 1)| <
          ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) / 4) *
            cliqueMainTerm n (density K) q (r + 1) (r + 1) := by
  have hnNat : 0 < n :=
    Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnNat
  obtain ⟨hdlo, hdhi⟩ := paper_host_density_bounds hqr hn K hd
  obtain ⟨hcap, hθ, hsmall⟩ := generator_cap_quarter_error_of_margin hqr hn hNb
  have hp : 0 < density K := (by positivity :
    (0 : ℝ) < (1 / 2 : ℝ) * (n : ℝ) ^ (-paperAlpha q (r + 1))).trans_le hdlo
  have hε : 0 < (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) / 4 := by positivity
  have hε1 : (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) / 4 ≤ 1 := by
    have hh : (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith only [paperAlpha_pos hqr])
    linarith only [hh]
  have hc0 := Real.rpow_nonneg hn0.le (-(1 / 10 : ℝ))
  have hsize : (q : ℝ) ≤ (2 * (n : ℝ) ^ (-(1 / 10 : ℝ)) -
      (n : ℝ) ^ (-(1 / 10 : ℝ))) * (Fintype.card (Fin n) * density K ^ q.choose (r + 1)) := by
    rw [Fintype.card_fin, show 2 * (n : ℝ) ^ (-(1 / 10 : ℝ)) -
      (n : ℝ) ^ (-(1 / 10 : ℝ)) = (n : ℝ) ^ (-(1 / 10 : ℝ)) by ring]
    exact modular_host_clique_size_paper_threshold hqr hn K hd
  simpa only [Fintype.card_fin] using exists_good_modular_generating_data N hN hT hqh hqr.le
    (by simpa only [Fintype.card_fin] using hnNat) hp (by linarith only [hc0]) (by positivity)
    (paper_host_error_small hqr hn) hsize
    ⌊(n : ℝ) ^ (1 - 7 * paperAlpha q (r + 1) / 10)⌋₊ hcap hε hε1
    (generator_count_quarter_error_paper_threshold hqr hn)
    (by simpa only [Fintype.card_fin] using hθ)
    (by simpa only [Fintype.card_fin] using hsmall (density K) hdhi)

theorem exists_good_modular_generators_quarter_paper_threshold {q r n h N : ℕ}
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
        ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) / 4) * (cliqueFamily K q).card ∧
      ((K \ C.good).card : ℝ) ≤
        ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) / 4) * K.card ∧
      ∀ e ∈ C.good,
        |((((cliqueFamily K q) \ C.saturated).filter fun Q => e.val ⊆ Q.val).card : ℝ) -
          cliqueMainTerm n (density K) q (r + 1) (r + 1)| <
          ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) / 4) *
            cliqueMainTerm n (density K) q (r + 1) (r + 1) := by
  exact exists_good_modular_generators_quarter_of_margin hqr hn hN
    (generator_modulus_margin_paper_threshold hqr hn hNb) hqh K hT hd

end Arxiv2411_18291
