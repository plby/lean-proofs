import Arxiv.Arxiv2411_18291.WeightedDecoderAtThreshold
import Arxiv.Arxiv2411_18291.VariableDecoderSplitting
import Arxiv.Arxiv2411_18291.VariableSplittingNumerics
import Arxiv.Arxiv2411_18291.SmallCarrierExchange

/-! # Constructed weighted decoder and splitting stages at n0

The generator need only have a sparse boundary, with no constant edge
multiplicity bound. All decoder and splitting inequalities are discharged,
and one fixed splitting family represents every generated leave. The later
cancellation stages are not part of this theorem.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_variable_splitting_paper_threshold
    {W : Type*} [Fintype W] [DecidableEq W] {q r n : ℕ}
    (S : ExchangeSystem W q (r + 1)) (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q)) (hS : S.graph.card ≤ (4 * q) ^ (2 * q))
    (D : Finset (Block (Fin n) q)) (C : Block (Fin n) q → ℕ)
    (B : Hypergraph (Fin n) (r + 1))
    (hD : IsCliqueCapacityBounded r D C ((n : ℝ) ^ (-(2 * paperAlpha q (r + 1) / 5))))
    (hB : IsGraphBounded B ((n : ℝ) ^ (-(2 * paperAlpha q (r + 1) / 5))))
    (hDB : cliqueSupport (r + 1) D ⊆ B) :
    Nonempty (VariableSplittingFamily S D B C ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 3)))) := by
  obtain ⟨d, hconflict, hnpos, hsize, hfree, hsmall, hfailure⟩ :=
    variable_splitting_paper_numerics hqr hn hw hS
  obtain ⟨F⟩ := exists_variable_splitting_family S hqr.le D C B (by positivity) hD hB hDB d
    (by simpa only [Fintype.card_fin] using hconflict)
    (by simpa only [Fintype.card_fin] using hnpos)
    (by simpa only [Fintype.card_fin] using hsize)
    (by simpa only [Fintype.card_fin] using hfree) hsmall
    (by simpa only [Block, Fintype.card_finset_len, Fintype.card_fin] using hfailure)
  exact ⟨{ F with bounded := F.bounded.mono (variable_splitting_output_density hqr hn hS) }⟩

theorem exists_weighted_decoder_splitting_paper_threshold
    {W : Type*} [Fintype W] [DecidableEq W] {q r n : ℕ}
    (S : ExchangeSystem W q (r + 1)) (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q)) (hS : S.graph.card ≤ (4 * q) ^ (2 * q))
    (D : Finset (Block (Fin n) q)) (B : Hypergraph (Fin n) (r + 1))
    (hDB : cliqueSupport (r + 1) D ⊆ B)
    (hD : IsCliqueFamilyBounded r D ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5))))
    (hB : IsGraphBounded B ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)))) :
    ∃ Z : B → Block (Fin n) (q + (r + 1)),
      IsCliqueCover (complete (Fin n) (r + 1) \ B) (fun e : B => e.val) Z ∧
      ∃ F : VariableSplittingFamily S (D ∪ cliqueRefinement q (univ.image Z))
          (cliqueCoverGraph (r := r) Z) (edgewiseDecoderCapacity D Z)
          ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 3))),
        ∀ L : Hypergraph (Fin n) (r + 1), L ⊆ B → GeneratedBy D (indicator L) →
          ∃ P N : Finset (Block (Fin n) q),
            P ⊆ exchangeSupport (fun s => S.map (F.embedding s)) ∧
            N ⊆ exchangeSupport (fun s => S.map (F.embedding s)) ∧ Disjoint P N ∧
            boundary (r + 1) (indicator P - indicator N) = indicator L := by
  obtain ⟨Z, hZ, hgraph, hcapacity⟩ := exists_weighted_decoder_paper_threshold hqr hn D B hD hB
  obtain ⟨F⟩ := exists_variable_splitting_paper_threshold S hqr hn hw hS
    (D ∪ cliqueRefinement q (univ.image Z)) (edgewiseDecoderCapacity D Z)
    (cliqueCoverGraph (r := r) Z) hcapacity hgraph (hZ.decoder_support_subset hDB)
  refine ⟨Z, hZ, F, ?_⟩
  intro L hLB hgen
  obtain ⟨Φ, hΦ, hs, hcap⟩ :=
    edgewise_representation_of_local_decoders hqr D B L hDB hLB Z hZ hgen
  obtain ⟨P, N, hP, hN, hdis, hboundary⟩ := F.signed_representation hqr.le Φ hcap hs
  exact ⟨P, N, hP, hN, hdis, hboundary.trans hΦ⟩

theorem exists_constructed_weighted_splitting_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (D : Finset (Block (Fin n) q)) (B : Hypergraph (Fin n) (r + 1))
    (hDB : cliqueSupport (r + 1) D ⊆ B)
    (hD : IsCliqueFamilyBounded r D ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5))))
    (hB : IsGraphBounded B ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)))) :
    ∃ T : FiniteExchangeSystem q (r + 1), ∃ A : Finset (Block T.Vertex q),
      IsExchangeFamily T.system A ∧ IsCrossSimple (r + 1) T.system.positive T.system.negative ∧
      IsPositiveFrameLocal T.system A ∧
      ∃ Z : B → Block (Fin n) (q + (r + 1)),
        IsCliqueCover (complete (Fin n) (r + 1) \ B) (fun e : B => e.val) Z ∧
        ∃ F : VariableSplittingFamily T.system (D ∪ cliqueRefinement q (univ.image Z))
            (cliqueCoverGraph (r := r) Z) (edgewiseDecoderCapacity D Z)
            ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 3))),
          ∀ L : Hypergraph (Fin n) (r + 1), L ⊆ B → GeneratedBy D (indicator L) →
            ∃ P N : Finset (Block (Fin n) q),
              P ⊆ exchangeSupport (fun s => T.system.map (F.embedding s)) ∧
              N ⊆ exchangeSupport (fun s => T.system.map (F.embedding s)) ∧ Disjoint P N ∧
              boundary (r + 1) (indicator P - indicator N) = indicator L := by
  classical
  obtain ⟨T, A, hsize, hA, hcross, hlocal, hw⟩ :=
    exists_small_carrier_clique_exchange q (r + 1) (Nat.succ_pos r) hqr
  exact ⟨T, A, hA, hcross, hlocal,
    exists_weighted_decoder_splitting_paper_threshold T.system hqr hn hw
      (hsize.trans (paper_exchange_graph_bound (Nat.succ_pos r) hqr)) D B hDB hD hB⟩

end Arxiv2411_18291
