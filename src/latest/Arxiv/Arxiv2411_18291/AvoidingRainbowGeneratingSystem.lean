import Arxiv.Arxiv2411_18291.RainbowAvoidingExtensions

/-!
# Sparse generation with avoidance of prescribed root colours

The initial palette is duplicated before invoking the rainbow-generation
theorem. Consequently the generating family spans every rainbow clique
in the duplicated palette, including those which use equal permutations
under different labels.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

variable {U W : Type*} [Fintype U] [Fintype W] [DecidableEq W] {q r : ℕ}

theorem eventually_exists_avoiding_rainbow_generating_system
    (F₀ : Block U (r + 1)) (hU : Fintype.card U = q)
    {S : ExchangeSystem W q (r + 1)} {A : Finset (Block W q)} (hA : IsExchangeFamily S A)
    {P₀ : Block W q} {e₀ : Block W (r + 1)} (hpair : IsEliminationPair S P₀ e₀)
    (hqr : r + 1 < q) (h N t : ℕ) (hN : 0 < N) (hqh : q.choose (r + 1) ≤ h)
    (hSh : S.graph.card ≤ h) {α : ℝ} (hα : 0 < α) (hαh : α * h ≤ 1 / 12) :
    ∃ u L : ℕ, ∀ᶠ n : ℕ in atTop, ∃ K : Hypergraph (Fin n) (r + 1),
      IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h ∧
      |density K - (n : ℝ) ^ (-α)| ≤
        (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-α) ∧
      ∃ C : ModularGeneratingData K (cliqueFamily K q) N,
        IsCliqueFamilyBounded r C.generators (2 ^ q * (n : ℝ) ^ (-(7 * α / 10))) ∧
        ((K \ C.good).card : ℝ) ≤ (n : ℝ) ^ (-(α / 10)) * K.card ∧
        ∃ σ : Fin (t + 1) × Fin u → Equiv.Perm (Fin n),
        ∃ ρ : Option ((Fin (t + 1) × Fin u) ⊕ (Fin L × S.farCliques)) → Equiv.Perm (Fin n),
          RainbowAvoidingExtensionProperties S P₀ σ C.good t ∧
          IsCliqueFamilyBounded r (permutedUnion ρ C.generators)
            ((((t + 1) * u + L * S.farCliques.card + 1 : ℕ) : ℝ) *
              (2 ^ q * (n : ℝ) ^ (-(7 * α / 10)))) ∧
          ∀ Q : Block (Fin n) q,
            IsRainbow (fun j => mapGraph (σ j).toEmbedding C.good) (cliqueEdges (r + 1) Q) →
            modularCliqueVector N (r + 1) Q ∈ generatedSubgroup
              (modularCliqueVector N (r + 1)) (permutedUnion ρ C.generators) := by
  obtain ⟨u, hext⟩ := eventually_combined_rainbow_extensions F₀ hU hpair h hqh hSh hα
    (by linarith only [hαh])
  obtain ⟨L, hgen⟩ := eventually_exists_rainbow_generating_family (J := Fin (t + 1) × Fin u)
    hA hqr h N hN hqh hSh hα hαh
  refine ⟨u, L, ?_⟩
  filter_upwards [hext, hgen] with n hnExt hnGen
  obtain ⟨K, hT, hlo, hd, C, hCb, hgood, hcol⟩ := hnGen
  obtain ⟨σ₀, hpunc, hclique, hpair⟩ := hnExt K hT hlo C.good C.good_subset hgood
  have hE : RainbowExtensionProperties S P₀ σ₀ C.good :=
    ⟨by simpa only [Fintype.card_fin] using hpunc, hclique, hpair⟩
  let σ (p : Fin (t + 1) × Fin u) := σ₀ p.2
  obtain ⟨ρ, hρ, _, hspan⟩ := hcol σ
  refine ⟨K, hT, hd, C, hCb, hgood, σ, ρ, hE.avoiding_copies t, ?_, hspan⟩
  simpa only [Fintype.card_prod, Fintype.card_fin] using hρ

end Arxiv2411_18291
