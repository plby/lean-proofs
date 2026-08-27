import Arxiv.Arxiv2411_18291.AllRanksPrintedColourPattern

/-!
# Constructing the entire printed-palette colour system in every rank

The exchange, typical host, sparse generating family and one successful
palette are all constructed. For that host the actual random permutation
experiment has joint failure at most n^(-1) for all four source conclusions.
-/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

theorem exists_sparse_printed_colour_system_all_ranks {q r n N : ℕ}
    [MeasurableSpace (Equiv.Perm (Fin n))]
    [MeasurableSingletonClass (Equiv.Perm (Fin n))]
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hN : 0 < N) (hNb : N ≤ (r + 1).factorial * q.choose (r + 1)) :
    ∃ T : FiniteExchangeSystem q (r + 1), ∃ A : Finset (Block T.Vertex q),
    ∃ P₀ : Block T.Vertex q, ∃ e₀ : Block T.Vertex (r + 1),
      IsExchangeFamily T.system A ∧ IsEliminationPair T.system P₀ e₀ ∧
      T.system.graph.card ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2 ∧
      Fintype.card T.Vertex ≤ (4 * q) ^ (2 * q) ∧
      ∃ K : Hypergraph (Fin n) (r + 1),
        IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) T.system.graph.card ∧
        |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
          (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)) ∧
        ∃ C : ModularGeneratingData K (cliqueFamily K q) N,
          IsCliqueFamilyBounded r C.generators
            (2 ^ q * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))) ∧
          ((K \ C.good).card : ℝ) ≤
            (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card ∧
          (RandomPermutation.probability
            (Fin (paperColourCount q (r + 1) T.system.graph.card)) (Fin n)).real
            {σ | ¬ PrintedColourSuccess T.system P₀ C σ} ≤ (n : ℝ) ^ (-1 : ℝ) ∧
          ∃ σ : Fin (paperColourCount q (r + 1) T.system.graph.card) → Equiv.Perm (Fin n),
            PrintedColourSuccess T.system P₀ C σ ∧
            IsCliqueFamilyBounded r (permutedUnion σ C.generators)
              ((paperColourCount q (r + 1) T.system.graph.card : ℝ) *
                (2 ^ q * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10)))) := by
  classical
  obtain ⟨T, A, P₀, e₀, hA, hpair, hT, hw, hfailure⟩ :=
    exists_printed_colour_pattern_all_ranks hqr hn
  have hqh : q.choose (r + 1) ≤ T.system.graph.card := by
    simpa only [card_cliqueEdges] using
      card_le_card (T.system.positive_decomposition.clique_subset T.system.base_mem)
  obtain ⟨K, hK, hd, C, hCb, _, hsat, hgood, hcount⟩ :=
    exists_sparse_modular_generators_paper_threshold hqr hn hN hNb hqh hT
  have hb := hfailure N K hK hd C hgood hsat (fun e he => (hcount e he).le)
  have hn1 : (1 : ℝ) < n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).trans_le hn
  obtain ⟨σ, hσ⟩ := IndependentTrials.exists_of_failure_lt_one _
    (hb.trans_lt (Real.rpow_lt_one_of_one_lt_of_neg hn1 (by norm_num)))
  have hM : 0 < T.system.graph.card := (Nat.choose_pos hqr.le).trans_le hqh
  have hu : 0 < paperColourCount q (r + 1) T.system.graph.card := by
    have hInv := paperInverseAlpha_pos hqr
    have hq : 0 < q := by omega
    unfold paperColourCount
    positivity
  have : Nonempty (Fin (paperColourCount q (r + 1) T.system.graph.card)) := ⟨⟨0, hu⟩⟩
  refine ⟨T, A, P₀, e₀, hA, hpair, hT, hw, K, hK, hd, C, hCb, hgood, hb, σ, hσ, ?_⟩
  simpa only [Fintype.card_fin] using hCb.permutedUnion σ

end Arxiv2411_18291
