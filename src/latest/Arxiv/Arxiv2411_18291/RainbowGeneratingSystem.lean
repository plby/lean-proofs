import Arxiv.Arxiv2411_18291.SparseRainbowGeneration
import Arxiv.Arxiv2411_18291.CombinedRainbowExtensions

/-!
# A sparse generating system with simultaneous rainbow extensions

The initial colour family has all three extension properties. A separate
enlarged family of permuted generators spans every clique rainbow in the
initial family. Both colour counts are fixed independently of the ambient
size, and the enlarged generating family remains polynomially sparse.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

variable {J U W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
variable {q r : ℕ}

structure RainbowExtensionProperties (S : ExchangeSystem W q (r + 1)) (N : Block W q)
    (σ : J → Equiv.Perm V) (G : Hypergraph V (r + 1)) : Prop where
  punctured : ∀ e : Block V (r + 1),
    ((3 / 8 : ℝ) * density G ^ (q.choose (r + 1) - 1) *
      (Fintype.card V : ℝ) ^ (q - (r + 1))) / (q - (r + 1)).factorial <
        (rainbowPuncturedCliques (fun i => mapGraph (σ i).toEmbedding G) e q).card
  clique : ∀ P : Block V q, ∃ f : W ↪ V, mapBlock f S.base = P ∧
    IsRainbow (fun i => mapGraph (σ i).toEmbedding G)
      (mapGraph f S.graph \ cliqueEdges (r + 1) P)
  pair : ∀ P Q : Block V q, ∀ d : Block V (r + 1), P.val ∩ Q.val = d.val →
    ∃ f : W ↪ V, mapBlock f S.base = P ∧ mapBlock f N = Q ∧
      IsRainbow (fun i => mapGraph (σ i).toEmbedding G)
        (mapGraph f S.graph \ (cliqueEdges (r + 1) P ∪ cliqueEdges (r + 1) Q))

omit [Fintype V] [DecidableEq V] in
theorem eventually_exists_rainbow_generating_system [Fintype U]
    (F₀ : Block U (r + 1)) (hU : Fintype.card U = q)
    {S : ExchangeSystem W q (r + 1)} {A : Finset (Block W q)} (hA : IsExchangeFamily S A)
    {P₀ : Block W q} {e₀ : Block W (r + 1)} (hpair : IsEliminationPair S P₀ e₀)
    (hqr : r + 1 < q) (h N : ℕ) (hN : 0 < N) (hqh : q.choose (r + 1) ≤ h)
    (hSh : S.graph.card ≤ h) {α : ℝ} (hα : 0 < α) (hαh : α * h ≤ 1 / 12) :
    ∃ u L : ℕ, ∀ᶠ n : ℕ in atTop, ∃ K : Hypergraph (Fin n) (r + 1),
      IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h ∧
      |density K - (n : ℝ) ^ (-α)| ≤
        (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-α) ∧
      ∃ C : ModularGeneratingData K (cliqueFamily K q) N,
        IsCliqueFamilyBounded r C.generators (2 ^ q * (n : ℝ) ^ (-(7 * α / 10))) ∧
        ((K \ C.good).card : ℝ) ≤ (n : ℝ) ^ (-(α / 10)) * K.card ∧
        ∃ σ : Fin u → Equiv.Perm (Fin n),
        ∃ ρ : Option (Fin u ⊕ (Fin L × S.farCliques)) → Equiv.Perm (Fin n),
          RainbowExtensionProperties S P₀ σ C.good ∧
          IsCliqueFamilyBounded r (permutedUnion ρ C.generators)
            (((u + L * S.farCliques.card + 1 : ℕ) : ℝ) *
              (2 ^ q * (n : ℝ) ^ (-(7 * α / 10)))) ∧
          ∀ Q : Block (Fin n) q,
            IsRainbow (fun j => mapGraph (σ j).toEmbedding C.good) (cliqueEdges (r + 1) Q) →
            modularCliqueVector N (r + 1) Q ∈ generatedSubgroup
              (modularCliqueVector N (r + 1)) (permutedUnion ρ C.generators) := by
  obtain ⟨u, hext⟩ := eventually_combined_rainbow_extensions F₀ hU hpair h hqh hSh hα
    (by linarith only [hαh])
  obtain ⟨L, hgen⟩ := eventually_exists_rainbow_generating_family (J := Fin u)
    hA hqr h N hN hqh hSh hα hαh
  refine ⟨u, L, ?_⟩
  filter_upwards [hext, hgen] with n hnExt hnGen
  obtain ⟨K, hT, hlo, hd, C, hCb, hgood, hcol⟩ := hnGen
  obtain ⟨σ, hpunc, hclique, hpair⟩ := hnExt K hT hlo C.good C.good_subset hgood
  obtain ⟨ρ, hρ, _, hspan⟩ := hcol σ
  refine ⟨K, hT, hd, C, hCb, hgood, σ, ρ, ⟨?_, hclique, hpair⟩, ?_, hspan⟩
  · simpa only [Fintype.card_fin] using hpunc
  · simpa only [Fintype.card_fin] using hρ

end Arxiv2411_18291
