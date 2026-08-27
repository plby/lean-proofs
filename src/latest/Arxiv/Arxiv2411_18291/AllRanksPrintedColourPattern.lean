import Arxiv.Arxiv2411_18291.PairPrintedColourProbability
import Arxiv.Arxiv2411_18291.SmallCarrierExchange

/-!
# A printed-palette colour pattern in every positive rank

For q at least three the general exchange construction suffices. For pairs
we use the four-vertex exchange and its exact fresh-colour counts. This
constructs the pattern as well as proving the joint colour probability.
-/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

def PrintedColourSuccess {W I : Type*} [Fintype W] [DecidableEq W] [Fintype I]
    {q r n N : ℕ} (S : ExchangeSystem W q (r + 1)) (P₀ : Block W q)
    {K : Hypergraph (Fin n) (r + 1)} (C : ModularGeneratingData K (cliqueFamily K q) N)
    (σ : I → Equiv.Perm (Fin n)) : Prop :=
  PaperRainbowExtensionProperties S P₀ σ C.good ∧
    ∀ Q : Block (Fin n) q,
      IsRainbow (fun j => mapGraph (σ j).toEmbedding C.good) (cliqueEdges (r + 1) Q) →
      modularCliqueVector N (r + 1) Q ∈
        generatedSubgroup (modularCliqueVector N (r + 1)) (permutedUnion σ C.generators)

def PrintedColourFailureBound {W : Type*} [Fintype W] [DecidableEq W]
    {q r n : ℕ} [MeasurableSpace (Equiv.Perm (Fin n))]
    [MeasurableSingletonClass (Equiv.Perm (Fin n))]
    (S : ExchangeSystem W q (r + 1)) (P₀ : Block W q) : Prop :=
  ∀ N : ℕ, ∀ K : Hypergraph (Fin n) (r + 1),
    IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) S.graph.card →
    |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)) →
    ∀ C : ModularGeneratingData K (cliqueFamily K q) N,
      ((K \ C.good).card : ℝ) ≤
        (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card →
      (C.saturated.card : ℝ) ≤
        (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * (cliqueFamily K q).card →
      (∀ e ∈ C.good,
        |((((cliqueFamily K q) \ C.saturated).filter fun Q => e.val ⊆ Q.val).card : ℝ) -
          cliqueMainTerm n (density K) q (r + 1) (r + 1)| ≤
            (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) *
              cliqueMainTerm n (density K) q (r + 1) (r + 1)) →
      (RandomPermutation.probability
        (Fin (paperColourCount q (r + 1) S.graph.card)) (Fin n)).real
        {σ | ¬ PrintedColourSuccess S P₀ C σ} ≤ (n : ℝ) ^ (-1 : ℝ)

theorem exists_printed_colour_pattern_all_ranks {q r n : ℕ}
    [MeasurableSpace (Equiv.Perm (Fin n))]
    [MeasurableSingletonClass (Equiv.Perm (Fin n))]
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n) :
    ∃ T : FiniteExchangeSystem q (r + 1), ∃ A : Finset (Block T.Vertex q),
    ∃ P₀ : Block T.Vertex q, ∃ e₀ : Block T.Vertex (r + 1),
      IsExchangeFamily T.system A ∧ IsEliminationPair T.system P₀ e₀ ∧
      T.system.graph.card ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2 ∧
      Fintype.card T.Vertex ≤ (4 * q) ^ (2 * q) ∧
      PrintedColourFailureBound (n := n) T.system P₀ := by
  classical
  by_cases hq : 3 ≤ q
  · obtain ⟨T, A, hT, hA, hcross, _, hw⟩ :=
      exists_small_carrier_clique_exchange q (r + 1) (Nat.succ_pos r) hqr
    obtain ⟨e₀, he₀⟩ := cliqueEdges_nonempty hqr.le T.system.base
    obtain ⟨P₀, hP₀, hPe⟩ := hA.2.2.1 e₀ he₀
    have hpair : IsEliminationPair T.system P₀ e₀ := by
      refine ⟨hA.1 hP₀, ?_, fun f hf => hA.pair_local hP₀ hf, hcross⟩
      rw [inter_comm]
      exact vertices_inter_eq_of_cliqueEdges_singleton (Nat.succ_pos r)
        P₀ T.system.base e₀ hPe
    have hqh : q.choose (r + 1) ≤ T.system.graph.card := by
      simpa only [card_cliqueEdges] using
        card_le_card (T.system.positive_decomposition.clique_subset T.system.base_mem)
    obtain ⟨f, _, hf⟩ := exists_subset_card_eq (s := (univ : Finset (Fin q)))
      (by simpa only [card_univ, Fintype.card_fin] using hqr.le)
    let F₀ : Block (Fin q) (r + 1) := ⟨f, hf⟩
    refine ⟨T, A, P₀, e₀, hA, hpair, hT, hw, ?_⟩
    intro N K hK hd C hgood hsat hcount
    exact printed_joint_rainbow_generation_failure_paper_threshold hqr hq hn
      F₀ (Fintype.card_fin _) hA hpair hw hqh le_rfl hT K hK hd C hgood hsat hcount
  · have hq2 : q = 2 := by omega
    have hr0 : r = 0 := by omega
    subst q r
    refine ⟨pairColourExchange.toFinite, {pairColourNearZero, pairColourNearOne},
      pairColourNearZero, pairColourEdge, pairColourExchange_exchange_family,
      pairColourExchange_elimination_pair, ?_, ?_, ?_⟩
    · change pairColourExchange.graph.card ≤ 3 * (2 * 2) ^ (0 + 1) * (Nat.choose 2 1) ^ 2
      rw [pairColourExchange_card]
      decide
    · change Fintype.card (Fin 4) ≤ (4 * 2) ^ (2 * 2)
      decide
    · intro N K hK hd C hgood hsat hcount
      exact pair_printed_joint_colour_failure_paper_threshold hn
        (by change 4 ≤ pairColourExchange.graph.card; rw [pairColourExchange_card])
        (by change pairColourExchange.graph.card ≤ 48; rw [pairColourExchange_card]; decide)
        K hK hd C hgood hsat hcount

end Arxiv2411_18291
