import Arxiv.Arxiv2411_18291.EliminationPattern
import Arxiv.Arxiv2411_18291.ExchangeFrameStructure
import Arxiv.Arxiv2411_18291.AllRanksColourTrials

/-!
# A four-vertex exchange for the pair-colouring case

The positive pairs are 01 and 23; the negative pairs are 02 and 13.
For edge rank one this is an exchange family and an elimination pattern.
Only two edges need fresh colours over a base pair, and only one over
the union of an opposite pair. These exact counts fit the printed palette.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

def pairColourBase : Block (Fin 4) 2 := ⟨{0, 1}, by decide⟩
def pairColourFar : Block (Fin 4) 2 := ⟨{2, 3}, by decide⟩
def pairColourNearZero : Block (Fin 4) 2 := ⟨{0, 2}, by decide⟩
def pairColourNearOne : Block (Fin 4) 2 := ⟨{1, 3}, by decide⟩
def pairColourEdge : Block (Fin 4) 1 := ⟨{0}, by decide⟩

def pairColourExchange : ExchangeSystem (Fin 4) 2 1 where
  graph := complete (Fin 4) 1
  positive := {pairColourBase, pairColourFar}
  negative := {pairColourNearZero, pairColourNearOne}
  positive_decomposition := by
    unfold IsDecomposition
    apply funext
    decide
  negative_decomposition := by
    unfold IsDecomposition
    apply funext
    decide
  disjoint := by decide
  base := pairColourBase
  base_mem := by decide

theorem pairColourExchange_exchange_family :
    IsExchangeFamily pairColourExchange {pairColourNearZero, pairColourNearOne} := by
  unfold IsExchangeFamily
  decide

theorem pairColourExchange_elimination_pair :
    IsEliminationPair pairColourExchange pairColourNearZero pairColourEdge := by
  constructor
  · decide
  · decide
  · decide
  · unfold IsCrossSimple
    decide

theorem pairColourExchange_card : pairColourExchange.graph.card = 4 := by decide

theorem pairColourExchange_base_new_edges :
    (newEdges pairColourExchange.base.val pairColourExchange.graph).card = 2 := by decide

theorem pairColourExchange_pair_new_edges :
    (newEdges (pairColourExchange.base.val ∪ pairColourNearZero.val)
      pairColourExchange.graph).card = 1 := by decide

theorem pairColourExchange_far_card : pairColourExchange.farCliques.card = 1 := by decide

theorem pairColourExchange_clique_palette :
    correctedCommonColourTrialCount 2 1 *
      (newEdges pairColourExchange.base.val pairColourExchange.graph).card ≤
        paperColourCount 2 1 pairColourExchange.graph.card := by
  rw [pairColourExchange_base_new_edges, pairColourExchange_card]
  unfold correctedCommonColourTrialCount paperColourCount
  omega

theorem pairColourExchange_pair_palette :
    correctedCommonColourTrialCount 2 1 *
      (newEdges (pairColourExchange.base.val ∪ pairColourNearZero.val)
        pairColourExchange.graph).card ≤
          paperColourCount 2 1 pairColourExchange.graph.card := by
  rw [pairColourExchange_pair_new_edges, pairColourExchange_card]
  unfold correctedCommonColourTrialCount paperColourCount
  omega

theorem pairColourExchange_punctured_palette :
    correctedCommonColourTrialCount 2 1 * (Nat.choose 2 1 - 1) ≤
      paperColourCount 2 1 pairColourExchange.graph.card := by
  rw [pairColourExchange_card]
  unfold correctedCommonColourTrialCount paperColourCount
  norm_num
  omega

theorem pairColourExchange_generation_palette :
    Nat.choose 2 1 + paperColourTrialCount 2 1 pairColourExchange.base.val.card *
      pairColourExchange.farCliques.card ≤ paperColourCount 2 1 pairColourExchange.graph.card := by
  rw [pairColourExchange.base.property, pairColourExchange_far_card, pairColourExchange_card]
  have hA : 0 < paperInverseAlpha 2 1 := paperInverseAlpha_pos (by decide)
  unfold paperColourTrialCount paperColourCount
  norm_num at ⊢
  omega

end Arxiv2411_18291
