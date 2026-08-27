import Arxiv.Arxiv2411_18291.RelaxedRainbowGeneration
import Arxiv.Arxiv2411_18291.EdgeCappedAtThreshold
import Arxiv.Arxiv2411_18291.RainbowGeneratingSystem

/-! # Constructed modular generation of rainbow cliques with retained edge caps

The host and capped generators are selected before the original palette.
For any such palette, added far-clique colours generate all its rainbow
cliques. Both caps grow only by the explicit number of colours.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_capped_rainbow_generating_family_paper_threshold
    {J W : Type*} [Fintype J] [Fintype W] [DecidableEq W] {q r n h N : ℕ}
    {S : ExchangeSystem W q (r + 1)} {A : Finset (Block W q)} (hA : IsExchangeFamily S A)
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hN : 0 < N) (hNb : N ≤ (r + 1).factorial * q.choose (r + 1))
    (hqh : q.choose (r + 1) ≤ h) (hSh : S.graph.card ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q)) :
    let L := logarithmicColourTrialCount n S.base.val.card
    ∃ K : Hypergraph (Fin n) (r + 1),
      IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h ∧
      (1 / 2 : ℝ) * (n : ℝ) ^ (-paperAlpha q (r + 1)) ≤ density K ∧
      |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
        (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)) ∧
      ∃ C : ModularGeneratingData K (cliqueFamily K q) N,
        IsCliqueFamilyBounded r C.generators
          (2 ^ q * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))) ∧
        (∀ e : Block (Fin n) (r + 1),
          ((C.generators.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤
            (n : ℝ) ^ (paperAlpha q (r + 1) / 20)) ∧
        ((K \ C.good).card : ℝ) ≤
          (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60)) * K.card ∧
        ∀ σ : J → Equiv.Perm (Fin n),
        ∃ ρ : Option (J ⊕ (Fin L × S.farCliques)) → Equiv.Perm (Fin n),
          IsCliqueFamilyBounded r (permutedUnion ρ C.generators)
            ((Fintype.card J + L * S.farCliques.card + 1 : ℕ) *
              (2 ^ q * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10)))) ∧
          (∀ e : Block (Fin n) (r + 1),
            (((permutedUnion ρ C.generators).filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤
              (Fintype.card J + L * S.farCliques.card + 1 : ℕ) *
                (n : ℝ) ^ (paperAlpha q (r + 1) / 20)) ∧
          (∀ Q ∈ permutedUnion σ C.generators, Q ∈ permutedUnion ρ C.generators) ∧
          ∀ Q : Block (Fin n) q,
            IsRainbow (fun j => mapGraph (σ j).toEmbedding C.good) (cliqueEdges (r + 1) Q) →
            modularCliqueVector N (r + 1) Q ∈ generatedSubgroup
              (modularCliqueVector N (r + 1)) (permutedUnion ρ C.generators) := by
  classical
  obtain ⟨K, hT, hd, C, hCb, hCap, _, hsat, hgood, hcount⟩ :=
    exists_sparse_edge_capped_modular_generators_paper_threshold hqr hn hN hNb hqh hH
  have hdlo := (paper_host_density_bounds hqr hn K hd).1
  refine ⟨K, hT, hdlo, hd, C, hCb, hCap, hgood, fun σ => ?_⟩
  obtain ⟨τ, hτ⟩ := sparse_host_rainbow_generation_relaxed_paper_threshold
    hA hqr hn hw hqh hSh hH K hT hd C hsat (fun e he => (hcount e he).le) σ
  let ρ := augmentedPermutation σ τ
  have hsub := permutedUnion_union_subset_augmented σ τ C.generators
  refine ⟨ρ, ?_, ?_, fun Q hQ => hsub (mem_union_left _ hQ), fun Q hQ => ?_⟩
  · simpa only [Fintype.card_option, Fintype.card_sum, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_coe] using hCb.permutedUnion ρ
  · intro e
    simpa only [Fintype.card_option, Fintype.card_sum, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_coe] using containing_permutedUnion_le ρ C.generators hCap e
  · exact generatedSubgroup_mono _ hsub (hτ Q hQ)

end Arxiv2411_18291
