import Arxiv.Arxiv2411_18291.SparseRainbowReplacements
import Arxiv.Arxiv2411_18291.ModularExchangeGeneration

/-!
# Generating the original rainbow cliques modulo an integer

The added colours generate the far cliques of successful exchanges; the
original colours generate their near cliques. The exchange identity then
generates every original rainbow base in the union of the two families of
permuted modular generators.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

variable {J I W V : Type*} [Fintype J] [Fintype I] [Fintype W] [DecidableEq W]
variable [Fintype V] [DecidableEq V] {q r N : ℕ}
variable {S : ExchangeSystem W q (r + 1)} {A : Finset (Block W q)}

omit [Fintype V] in
theorem ModularGeneratingData.generated_of_exchange_replacements [Finite V]
    {K : Hypergraph V (r + 1)} {D : Finset (Block V q)} (C : ModularGeneratingData K D N)
    (σ : J → Equiv.Perm V) (τ : I → Equiv.Perm V) (f : W ↪ V)
    (hrep : ∀ P ∈ S.replacementCliques,
      mapBlock f P ∈ permutedUnion σ (D \ C.saturated) ∪
        permutedUnion τ (D \ C.saturated)) :
    modularCliqueVector N (r + 1) (mapBlock f S.base) ∈
      generatedSubgroup (modularCliqueVector N (r + 1))
        (permutedUnion σ C.generators ∪ permutedUnion τ C.generators) := by
  apply S.modular_image_base_mem N f
  intro P hP
  rcases mem_union.mp (hrep P hP) with hσ | hτ
  · exact generatedSubgroup_mono _ subset_union_left (C.permuted_generates σ hσ)
  · exact generatedSubgroup_mono _ subset_union_right (C.permuted_generates τ hτ)

omit [Fintype I] [Fintype V] [DecidableEq V] in
theorem eventually_sparse_host_rainbow_generation (hA : IsExchangeFamily S A)
    (hqr : r + 1 < q) (h : ℕ) (hqh : q.choose (r + 1) ≤ h) (hSh : S.graph.card ≤ h)
    {α : ℝ} (hα : 0 < α) (hαh : α * h ≤ 1 / 12) :
    ∃ L : ℕ, ∀ᶠ n : ℕ in atTop, ∀ K : Hypergraph (Fin n) (r + 1),
      IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h →
      (1 / 2 : ℝ) * (n : ℝ) ^ (-α) ≤ density K →
      ∀ C : ModularGeneratingData K (cliqueFamily K q) N,
      (C.saturated.card : ℝ) ≤ (n : ℝ) ^ (-(α / 10)) * (cliqueFamily K q).card →
      (∀ e ∈ C.good,
        |((((cliqueFamily K q) \ C.saturated).filter fun Q => e.val ⊆ Q.val).card : ℝ) -
          cliqueMainTerm n (density K) q (r + 1) (r + 1)| ≤
            (n : ℝ) ^ (-(α / 10)) * cliqueMainTerm n (density K) q (r + 1) (r + 1)) →
      ∀ σ : J → Equiv.Perm (Fin n),
      ∃ τ : Fin L × S.farCliques → Equiv.Perm (Fin n), ∀ Q : Block (Fin n) q,
        IsRainbow (fun j => mapGraph (σ j).toEmbedding C.good) (cliqueEdges (r + 1) Q) →
        modularCliqueVector N (r + 1) Q ∈
          generatedSubgroup (modularCliqueVector N (r + 1))
            (permutedUnion σ C.generators ∪ permutedUnion τ C.generators) := by
  obtain ⟨L, hL⟩ := eventually_sparse_host_rainbow_replacements (J := J)
    hA hqr h hqh hSh hα hαh
  refine ⟨L, ?_⟩
  filter_upwards [hL] with n hn
  intro K hT hd C hsat hcount σ
  have hdel : (cliqueFamily K q) \ ((cliqueFamily K q) \ C.saturated) ⊆ C.saturated := by
    intro Q hQ
    by_contra hQS
    exact (mem_sdiff.mp hQ).2 (mem_sdiff.mpr ⟨(mem_sdiff.mp hQ).1, hQS⟩)
  have hloss : (((cliqueFamily K q) \ ((cliqueFamily K q) \ C.saturated)).card : ℝ) ≤
      (n : ℝ) ^ (-(α / 10)) * (cliqueFamily K q).card :=
    (Nat.cast_le.mpr (card_le_card hdel)).trans hsat
  obtain ⟨τ, hτ⟩ := hn K hT hd ((cliqueFamily K q) \ C.saturated) sdiff_subset hloss
    C.good hcount σ
  refine ⟨τ, fun Q hQ => ?_⟩
  obtain ⟨f, hf, hrep⟩ := hτ Q hQ
  rw [← hf]
  exact C.generated_of_exchange_replacements σ τ f hrep

end Arxiv2411_18291
