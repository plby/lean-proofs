import Arxiv.Arxiv2411_18291.FiniteSparseModularGenerators
import Arxiv.Arxiv2411_18291.AvoidingRainbowGeneratingSystem
import Arxiv.Arxiv2411_18291.FiniteCombinedRainbowExtensions
import Arxiv.Arxiv2411_18291.FiniteRainbowReplacements

/-!
# Colour-system assembly using a finite typical and modular host

The typical graph and sparse modular generators are constructed at n0.
All three extension palettes and the far-clique replacement experiment
are also constructed at n0, with explicit finite palette sizes.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

variable {J W : Type*} [Fintype J] [Fintype W] [DecidableEq W] {q r : ℕ}
variable {S : ExchangeSystem W q (r + 1)} {A : Finset (Block W q)}

theorem exists_paper_rainbow_generating_family_threshold (hA : IsExchangeFamily S A)
    (hqr : r + 1 < q) (h N : ℕ) (hN : 0 < N) (hqh : q.choose (r + 1) ≤ h)
    (hSh : S.graph.card ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (hNb : N ≤ (r + 1).factorial * q.choose (r + 1))
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q)) {n : ℕ}
    (hn : paperSizeThreshold q (r + 1) ≤ n) :
    let L := paperColourTrialCount q (r + 1) S.base.val.card
    ∃ K : Hypergraph (Fin n) (r + 1),
      IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h ∧
      (1 / 2 : ℝ) * (n : ℝ) ^ (-paperAlpha q (r + 1)) ≤ density K ∧
      |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
        (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)) ∧
      ∃ C : ModularGeneratingData K (cliqueFamily K q) N,
        IsCliqueFamilyBounded r C.generators
          (2 ^ q * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))) ∧
        ((K \ C.good).card : ℝ) ≤ (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card ∧
        ∀ σ : J → Equiv.Perm (Fin n),
        ∃ ρ : Option (J ⊕ (Fin L × S.farCliques)) → Equiv.Perm (Fin n),
          IsCliqueFamilyBounded r (permutedUnion ρ C.generators)
            (((Fintype.card J + L * S.farCliques.card + 1 : ℕ) : ℝ) *
              (2 ^ q * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10)))) ∧
          (∀ Q ∈ permutedUnion σ C.generators, Q ∈ permutedUnion ρ C.generators) ∧
          ∀ Q : Block (Fin n) q,
            IsRainbow (fun j => mapGraph (σ j).toEmbedding C.good) (cliqueEdges (r + 1) Q) →
            modularCliqueVector N (r + 1) Q ∈ generatedSubgroup
              (modularCliqueVector N (r + 1)) (permutedUnion ρ C.generators) := by
  classical
  obtain ⟨K, hT, hd, C, hCb, _, hsat, hgood, hcount⟩ :=
    exists_sparse_modular_generators_paper_threshold hqr hn hN hNb hqh hH
  have hdlo := (paper_host_density_bounds hqr hn K hd).1
  refine ⟨K, hT, hdlo, hd, C, hCb, hgood, fun σ => ?_⟩
  obtain ⟨τ, hτ⟩ := sparse_host_rainbow_generation_paper_threshold hA hqr hn hw hqh hSh hH
    K hT hd C hsat (fun e he => (hcount e he).le) σ
  let ρ := augmentedPermutation σ τ
  have hsub := permutedUnion_union_subset_augmented σ τ C.generators
  refine ⟨ρ, ?_, fun Q hQ => hsub (mem_union_left _ hQ), fun Q hQ => ?_⟩
  · simpa only [Fintype.card_option, Fintype.card_sum, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_coe] using hCb.permutedUnion ρ
  · exact generatedSubgroup_mono _ hsub (hτ Q hQ)

theorem eventually_exists_paper_rainbow_generating_family (hA : IsExchangeFamily S A)
    (hqr : r + 1 < q) (h N : ℕ) (hN : 0 < N) (hqh : q.choose (r + 1) ≤ h)
    (hSh : S.graph.card ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (hNb : N ≤ (r + 1).factorial * q.choose (r + 1))
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q)) :
    ∃ L : ℕ, ∀ᶠ n : ℕ in atTop, ∃ K : Hypergraph (Fin n) (r + 1),
      IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h ∧
      (1 / 2 : ℝ) * (n : ℝ) ^ (-paperAlpha q (r + 1)) ≤ density K ∧
      |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
        (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)) ∧
      ∃ C : ModularGeneratingData K (cliqueFamily K q) N,
        IsCliqueFamilyBounded r C.generators
          (2 ^ q * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))) ∧
        ((K \ C.good).card : ℝ) ≤ (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card ∧
        ∀ σ : J → Equiv.Perm (Fin n),
        ∃ ρ : Option (J ⊕ (Fin L × S.farCliques)) → Equiv.Perm (Fin n),
          IsCliqueFamilyBounded r (permutedUnion ρ C.generators)
            (((Fintype.card J + L * S.farCliques.card + 1 : ℕ) : ℝ) *
              (2 ^ q * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10)))) ∧
          (∀ Q ∈ permutedUnion σ C.generators, Q ∈ permutedUnion ρ C.generators) ∧
          ∀ Q : Block (Fin n) q,
            IsRainbow (fun j => mapGraph (σ j).toEmbedding C.good) (cliqueEdges (r + 1) Q) →
            modularCliqueVector N (r + 1) Q ∈ generatedSubgroup
              (modularCliqueVector N (r + 1)) (permutedUnion ρ C.generators) := by
  refine ⟨paperColourTrialCount q (r + 1) S.base.val.card, ?_⟩
  filter_upwards [eventually_ge_atTop (paperSizeThreshold q (r + 1))] with n hn
  exact exists_paper_rainbow_generating_family_threshold hA hqr h N hN hqh hSh hH hNb hw hn

variable {U : Type*} [Fintype U]

theorem exists_paper_avoiding_rainbow_generating_system_threshold
    (F₀ : Block U (r + 1)) (hU : Fintype.card U = q)
    {S : ExchangeSystem W q (r + 1)} {A : Finset (Block W q)} (hA : IsExchangeFamily S A)
    {P₀ : Block W q} {e₀ : Block W (r + 1)} (hpair : IsEliminationPair S P₀ e₀)
    (hqr : r + 1 < q) (h N t : ℕ) (hN : 0 < N) (hqh : q.choose (r + 1) ≤ h)
    (hSh : S.graph.card ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (hNb : N ≤ (r + 1).factorial * q.choose (r + 1))
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q)) {n : ℕ}
    (hn : paperSizeThreshold q (r + 1) ≤ n) :
    let u := paperExtensionPaletteSize S P₀
    let L := paperColourTrialCount q (r + 1) S.base.val.card
    ∃ K : Hypergraph (Fin n) (r + 1),
      IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h ∧
      |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
        (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)) ∧
      ∃ C : ModularGeneratingData K (cliqueFamily K q) N,
        IsCliqueFamilyBounded r C.generators
          (2 ^ q * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))) ∧
        ((K \ C.good).card : ℝ) ≤ (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card ∧
        ∃ σ : Fin (t + 1) × Fin u → Equiv.Perm (Fin n),
        ∃ ρ : Option ((Fin (t + 1) × Fin u) ⊕ (Fin L × S.farCliques)) → Equiv.Perm (Fin n),
          RainbowAvoidingExtensionProperties S P₀ σ C.good t ∧
          IsCliqueFamilyBounded r (permutedUnion ρ C.generators)
            ((((t + 1) * u + L * S.farCliques.card + 1 : ℕ) : ℝ) *
              (2 ^ q * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10)))) ∧
          ∀ Q : Block (Fin n) q,
            IsRainbow (fun j => mapGraph (σ j).toEmbedding C.good) (cliqueEdges (r + 1) Q) →
            modularCliqueVector N (r + 1) Q ∈ generatedSubgroup
              (modularCliqueVector N (r + 1)) (permutedUnion ρ C.generators) := by
  classical
  let u := paperExtensionPaletteSize S P₀
  obtain ⟨K, hT, _, hd, C, hCb, hgood, hcol⟩ :=
    exists_paper_rainbow_generating_family_threshold (J := Fin (t + 1) × Fin u)
      hA hqr h N hN hqh hSh hH hNb hw hn
  obtain ⟨σ₀, hpunc, hclique, hpair⟩ := combined_rainbow_extensions_paper_threshold
    hqr hn F₀ hU hpair hw hqh hSh hH K C.good hT hd C.good_subset hgood
  have hE : RainbowExtensionProperties S P₀ σ₀ C.good :=
    ⟨by simpa only [Fintype.card_fin] using hpunc, hclique, hpair⟩
  let σ (p : Fin (t + 1) × Fin u) := σ₀ p.2
  obtain ⟨ρ, hρ, _, hspan⟩ := hcol σ
  refine ⟨K, hT, hd, C, hCb, hgood, σ, ρ, hE.avoiding_copies t, ?_, hspan⟩
  simpa only [Fintype.card_prod, Fintype.card_fin] using hρ

theorem eventually_exists_paper_avoiding_rainbow_generating_system
    (F₀ : Block U (r + 1)) (hU : Fintype.card U = q)
    {S : ExchangeSystem W q (r + 1)} {A : Finset (Block W q)} (hA : IsExchangeFamily S A)
    {P₀ : Block W q} {e₀ : Block W (r + 1)} (hpair : IsEliminationPair S P₀ e₀)
    (hqr : r + 1 < q) (h N t : ℕ) (hN : 0 < N) (hqh : q.choose (r + 1) ≤ h)
    (hSh : S.graph.card ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (hNb : N ≤ (r + 1).factorial * q.choose (r + 1))
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q)) :
    ∃ u L : ℕ, ∀ᶠ n : ℕ in atTop, ∃ K : Hypergraph (Fin n) (r + 1),
      IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h ∧
      |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
        (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)) ∧
      ∃ C : ModularGeneratingData K (cliqueFamily K q) N,
        IsCliqueFamilyBounded r C.generators
          (2 ^ q * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))) ∧
        ((K \ C.good).card : ℝ) ≤ (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card ∧
        ∃ σ : Fin (t + 1) × Fin u → Equiv.Perm (Fin n),
        ∃ ρ : Option ((Fin (t + 1) × Fin u) ⊕ (Fin L × S.farCliques)) → Equiv.Perm (Fin n),
          RainbowAvoidingExtensionProperties S P₀ σ C.good t ∧
          IsCliqueFamilyBounded r (permutedUnion ρ C.generators)
            ((((t + 1) * u + L * S.farCliques.card + 1 : ℕ) : ℝ) *
              (2 ^ q * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10)))) ∧
          ∀ Q : Block (Fin n) q,
            IsRainbow (fun j => mapGraph (σ j).toEmbedding C.good) (cliqueEdges (r + 1) Q) →
            modularCliqueVector N (r + 1) Q ∈ generatedSubgroup
              (modularCliqueVector N (r + 1)) (permutedUnion ρ C.generators) := by
  refine ⟨paperExtensionPaletteSize S P₀,
    paperColourTrialCount q (r + 1) S.base.val.card, ?_⟩
  filter_upwards [eventually_ge_atTop (paperSizeThreshold q (r + 1))] with n hn
  exact exists_paper_avoiding_rainbow_generating_system_threshold
    F₀ hU hA hpair hqr h N t hN hqh hSh hH hNb hw hn

end Arxiv2411_18291
