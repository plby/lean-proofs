import Arxiv.Arxiv2411_18291.CappedRainbowGeneratingFamily
import Arxiv.Arxiv2411_18291.RelaxedCombinedRainbowExtensions
import Arxiv.Arxiv2411_18291.RelaxedGoodDensity
import Arxiv.Arxiv2411_18291.RainbowAvoidingExtensions
import Arxiv.Arxiv2411_18291.RepeatedColourBounds

/-! # A full avoiding rainbow generating system with retained caps

The three extension palettes, avoiding copies, and far-clique generation
all use the same constructed host. Repeated labels used for avoidance do
not add generator cliques, so the caps are independent of the number of
avoiding copies. The remaining palette factor is explicit.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_capped_avoiding_rainbow_generating_system_paper_threshold
    {U W : Type*} [Fintype U] [Fintype W] [DecidableEq W] {q r n : ℕ}
    (F₀ : Block U (r + 1)) (hU : Fintype.card U = q)
    {S : ExchangeSystem W q (r + 1)} {A : Finset (Block W q)} (hA : IsExchangeFamily S A)
    {P₀ : Block W q} {e₀ : Block W (r + 1)} (hpair : IsEliminationPair S P₀ e₀)
    (hqr : r + 1 < q) (h N t : ℕ) (hN : 0 < N) (hqh : q.choose (r + 1) ≤ h)
    (hSh : S.graph.card ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (hNb : N ≤ (r + 1).factorial * q.choose (r + 1))
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q))
    (hn : paperSizeThreshold q (r + 1) ≤ n) :
    let u := relaxedExtensionPaletteSize n S P₀
    let L := logarithmicColourTrialCount n S.base.val.card
    ∃ K : Hypergraph (Fin n) (r + 1),
      IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h ∧
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
        (∀ s ≤ h, (1 / 2 : ℝ) * ((n : ℝ) ^ (-paperAlpha q (r + 1))) ^ s ≤
          density C.good ^ s) ∧
        ∃ σ : Fin (t + 1) × Fin u → Equiv.Perm (Fin n),
        ∃ ρ : Option ((Fin (t + 1) × Fin u) ⊕ (Fin L × S.farCliques)) → Equiv.Perm (Fin n),
          RainbowAvoidingExtensionProperties S P₀ σ C.good t ∧
          IsCliqueFamilyBounded r (permutedUnion ρ C.generators)
            ((u + L * S.farCliques.card + 1 : ℕ) *
              (2 ^ q * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10)))) ∧
          (∀ e : Block (Fin n) (r + 1),
            (((permutedUnion ρ C.generators).filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤
              (u + L * S.farCliques.card + 1 : ℕ) *
                (n : ℝ) ^ (paperAlpha q (r + 1) / 20)) ∧
          ∀ Q : Block (Fin n) q,
            IsRainbow (fun j => mapGraph (σ j).toEmbedding C.good) (cliqueEdges (r + 1) Q) →
            modularCliqueVector N (r + 1) Q ∈ generatedSubgroup
              (modularCliqueVector N (r + 1)) (permutedUnion ρ C.generators) := by
  classical
  let u := relaxedExtensionPaletteSize n S P₀
  obtain ⟨K, hT, hd, C, hCb, hCap, _, hsat, hgood, hcount⟩ :=
    exists_sparse_edge_capped_modular_generators_paper_threshold hqr hn hN hNb hqh hH
  obtain ⟨σ₀, hpunc, hclique, hpair'⟩ := combined_rainbow_extensions_relaxed_paper_threshold
    hqr hn F₀ hU hpair hw hqh hSh hH K C.good hT hd C.good_subset hgood
  have hE : RainbowExtensionProperties S P₀ σ₀ C.good :=
    ⟨by simpa only [Fintype.card_fin] using hpunc, hclique, hpair'⟩
  let σ (p : Fin (t + 1) × Fin u) := σ₀ p.2
  obtain ⟨τ, hτ⟩ := sparse_host_rainbow_generation_relaxed_paper_threshold
    hA hqr hn hw hqh hSh hH K hT hd C hsat (fun e he => (hcount e he).le) σ
  let ρ := augmentedPermutation σ τ
  have hρeq : permutedUnion ρ C.generators =
      permutedUnion (augmentedPermutation σ₀ τ) C.generators :=
    permutedUnion_augmented_repeated (T := Fin (t + 1)) σ₀ τ C.generators
  have hsub := permutedUnion_union_subset_augmented σ τ C.generators
  have hpowers (s : ℕ) (hs : s ≤ h) := good_reference_density_power_relaxed_paper_threshold
    hqr hn ((Nat.choose_pos hqr.le).trans_le hqh) hH hs K C.good hd C.good_subset hgood
  refine ⟨K, hT, hd, C, hCb, hCap, hgood, hpowers, σ, ρ, hE.avoiding_copies t, ?_, ?_, ?_⟩
  · rw [hρeq]
    simpa only [Fintype.card_option, Fintype.card_sum, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_coe] using hCb.permutedUnion (augmentedPermutation σ₀ τ)
  · intro e
    rw [hρeq]
    simpa only [Fintype.card_option, Fintype.card_sum, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_coe] using
        containing_permutedUnion_le (augmentedPermutation σ₀ τ) C.generators hCap e
  · intro Q hQ
    exact generatedSubgroup_mono _ hsub (hτ Q hQ)

end Arxiv2411_18291
