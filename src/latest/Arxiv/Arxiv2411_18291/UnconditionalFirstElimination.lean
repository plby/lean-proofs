import Arxiv.Arxiv2411_18291.CappedFirstElimination
import Arxiv.Arxiv2411_18291.VariableFirstCancellation

/-! # Constructed first universal cancellation at the original threshold

The exchange patterns, generators, decoders, fixed splitting family, and
elimination copies for every opposite near pair are all constructed from
the sparse source graph. The further cancellation stage is not included.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_unconditional_first_elimination_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hq : 3 ≤ q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (B : Hypergraph (Fin n) (r + 1))
    (hB : IsGraphBounded B ((n : ℝ) ^ (-paperRho q (r + 1)))) :
    ∃ D : Finset (Block (Fin n) q),
      IsCliqueFamilyBounded r D ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5))) ∧
      IsGraphBounded (B ∪ cliqueSupport (r + 1) D)
        ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5))) ∧
      ∃ T : FiniteExchangeSystem q (r + 1), ∃ A : Finset (Block T.Vertex q),
        IsExchangeFamily T.system A ∧
        IsCrossSimple (r + 1) T.system.positive T.system.negative ∧
        IsPositiveFrameLocal T.system A ∧
        ∃ Z : ↥(B ∪ cliqueSupport (r + 1) D) → Block (Fin n) (q + (r + 1)),
          IsCliqueCover (complete (Fin n) (r + 1) \ (B ∪ cliqueSupport (r + 1) D))
            (fun e : ↥(B ∪ cliqueSupport (r + 1) D) => e.val) Z ∧
          ∃ F : VariableSplittingFamily T.system (D ∪ cliqueRefinement q (univ.image Z))
              (cliqueCoverGraph (r := r) Z) (edgewiseDecoderCapacity D Z)
              ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 2))),
            IsCliqueFamilyBounded r F.cliques
              ((n : ℝ) ^ (-(89 * paperAlpha q (r + 1) / 180))) ∧
            (∀ e : Block (Fin n) (r + 1),
              ((F.cliques.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤
                (n : ℝ) ^ (7 * paperAlpha q (r + 1) / 60)) ∧
            ∃ U : FiniteExchangeSystem q (r + 1), ∃ N₀ : Block U.Vertex q,
              ∃ e₀ : Block U.Vertex (r + 1), IsEliminationPair U.system N₀ e₀ ∧
                U.system.graph.card ≤ (4 * q) ^ (2 * q) ∧
                Fintype.card U.Vertex ≤ (4 * q) ^ (2 * q) ∧
                ∃ E : EliminationFamily U.system N₀ F.graph F.pairPositive F.pairNegative
                    ((n : ℝ) ^ (-(17 * paperAlpha q (r + 1) / 45)) +
                      U.system.graph.card * (4 * (r + 1).factorial *
                        (n : ℝ) ^ (-(17 * paperAlpha q (r + 1) / 45)))),
                  IsGraphBounded E.graph ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 3))) ∧
            ∀ L : Hypergraph (Fin n) (r + 1), L ⊆ B →
              IntegrallyDecomposable q (indicator L) →
              ∃ P N : Finset (Block (Fin n) q),
                P ⊆ F.positiveCliques ∧ N ⊆ F.negativeCliques ∧ Disjoint P N ∧
                boundary (r + 1) (indicator P - indicator N) = indicator L ∧
                ∃ M : VariableNearMatching F P N,
                  Disjoint (E.replacePositive M.selected P) (E.replaceNegative M.selected N) ∧
                  boundary (r + 1) (indicator (E.replacePositive M.selected P) -
                    indicator (E.replaceNegative M.selected N)) = indicator L ∧
                  E.replaceNegative M.selected N ⊆ F.negativeFar ∪ E.negativeCliques := by
  obtain ⟨D, hD, hsupport, T, A, hA, hcross, hlocal, Z, hZ, F, hF, hcap, hout⟩ :=
    exists_unconditional_sharp_capped_variable_splitting_paper_threshold hqr hq hn B hB
  obtain ⟨U, N₀, e₀, hpair, hU, hw⟩ := exists_small_carrier_elimination_pattern q r hqr
  have hU' := hU.trans (paper_exchange_graph_bound (Nat.succ_pos r) hqr)
  obtain ⟨E, hE⟩ := exists_capped_first_elimination_with_bounds_paper_threshold
    hA F hqr hn hF hcap U.system N₀ e₀ hpair hw hU'
  refine ⟨D, hD, hsupport, T, A, hA, hcross, hlocal, Z, hZ, F, hF, hcap,
    U, N₀, e₀, hpair, hU', hw, E, hE, ?_⟩
  intro L hLB hInt
  obtain ⟨P, N, hP, hN, hdis, hb, ⟨M⟩⟩ := hout L hLB hInt
  exact ⟨P, N, hP, hN, hdis, hb, M, M.first_signs_disjoint E hpair hqr.le hP hN,
    (M.first_boundary E hpair hqr.le hP hN).trans hb, M.first_negative_subset E hN⟩

end Arxiv2411_18291
