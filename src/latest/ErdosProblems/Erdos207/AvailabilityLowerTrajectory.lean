/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.OutsideTrackableSupply
import ErdosProblems.Erdos207.GreedyCoveringChoiceCount

/-!
# The global availability lower trajectory

The lower pair trajectory also controls total availability.  Indeed, every
uncovered pair outside the absorber graph and outside the flexible square is
alive, so a pair-star floor supplies that many available triples through the
pair.  Double counting pair--triple incidences loses only the factor three.

Unlike the averaged availability martingale, this estimate retains the
cubic trajectory all the way through the long initial phase.
-/

namespace Erdos207

open Finset

noncomputable section

/-- The currently uncovered pairs to which `OutsideLeavePairsAlive` applies. -/
def outsideLiveUncoveredEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (S : GreedyStateOn V) :
    Finset (Sym2 V) :=
  outsideTrackablePart H X
    (greedyUncoveredEdges (graphEdges (SimpleGraph.completeGraph V)) S)

/-- A packing has exactly three covered complete-graph edges per chosen
triangle, so its complete-graph uncovered set has the expected exact size. -/
lemma card_greedyUncoveredEdges_complete
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : GreedyStateOn V)
    (hpacking : IsPackingOn S.chosen) :
    (greedyUncoveredEdges
        (graphEdges (SimpleGraph.completeGraph V)) S).card =
      Nat.choose (Fintype.card V) 2 - 3 * S.chosen.card := by
  classical
  have hcovered : graphEdges (coveredGraph S.chosen) ⊆
      graphEdges (SimpleGraph.completeGraph V) := by
    intro e he
    rw [mem_graphEdges_iff] at he ⊢
    exact mem_graphEdges_iff.mp
      (mem_graphEdges_completeGraph_iff_not_isDiag.mpr
        ((coveredGraph S.chosen).not_isDiag_of_mem_edgeSet he))
  rw [greedyUncoveredEdges, card_sdiff_of_subset hcovered]
  congr 1
  · rw [graphEdges_eq_edgeFinset,
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  · rw [graphEdges_eq_edgeFinset, coveredGraph_edgeFinset_eq_biUnion,
      card_biUnion_tripleEdgeFinset_of_isPackingOn hpacking]

/-- Removing absorber edges and pairs internal to `X` costs at most the
cardinalities of those two explicit exceptional families.  We deliberately
use `X.sym2`, which also contains the diagonal, because the harmless coarse
bound keeps subsequent natural-number arithmetic simple. -/
lemma uncovered_sub_exceptions_le_outsideLiveUncoveredEdges_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (S : GreedyStateOn V) :
    (greedyUncoveredEdges
          (graphEdges (SimpleGraph.completeGraph V)) S).card -
        (graphEdges H).card - X.sym2.card ≤
      (outsideLiveUncoveredEdges H X S).card := by
  classical
  let E := greedyUncoveredEdges
    (graphEdges (SimpleGraph.completeGraph V)) S
  let B := outsideLiveUncoveredEdges H X S
  have hBE : B ⊆ E := by
    intro e he
    exact outsideTrackablePart_subset H X E he
  have hremoved : E \ B ⊆ graphEdges H ∪ X.sym2 := by
    intro e he
    have heE : e ∈ E := (mem_sdiff.mp he).1
    have heB : e ∉ B := (mem_sdiff.mp he).2
    have hoff : ¬ e.IsDiag := by
      have heComplete := (mem_sdiff.mp heE).1
      exact mem_graphEdges_completeGraph_iff_not_isDiag.mp heComplete
    by_cases heH : e ∈ graphEdges H
    · exact mem_union_left _ heH
    · apply mem_union_right
      rw [mem_sym2_iff]
      intro x hxe
      have hxfin : x ∈ e.toFinset := Sym2.mem_toFinset.mpr hxe
      by_contra hxX
      apply heB
      change e ∈ E.filter (fun f ↦
        ¬ f.IsDiag ∧ f ∉ graphEdges H ∧ ¬ f.toFinset ⊆ X)
      rw [mem_filter]
      refine ⟨heE, hoff, heH, ?_⟩
      intro hsub
      exact hxX (hsub hxfin)
  have hremovedCard : (E \ B).card ≤
      (graphEdges H).card + X.sym2.card := by
    exact (card_le_card hremoved).trans (card_union_le _ _)
  have hsplit := card_sdiff_add_card_eq_card hBE
  change E.card - (graphEdges H).card - X.sym2.card ≤ B.card
  omega

/-- Explicit clock form of the preceding estimate. -/
theorem choose_sub_chosen_sub_exceptions_le_outsideLiveUncoveredEdges_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (S : GreedyStateOn V) (hpacking : IsPackingOn S.chosen) :
    Nat.choose (Fintype.card V) 2 - 3 * S.chosen.card -
        (graphEdges H).card - X.sym2.card ≤
      (outsideLiveUncoveredEdges H X S).card := by
  rw [← card_greedyUncoveredEdges_complete S hpacking]
  exact uncovered_sub_exceptions_le_outsideLiveUncoveredEdges_card H X S

/-- A pair-star floor supplies every currently uncovered outside pair. -/
lemma outsideLiveUncoveredEdges_pairSupply
    {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {X : Finset V} {S : GreedyStateOn V} {d : ℕ}
    (hfloor : HasAvailablePairFloor d S)
    (houtside : OutsideLeavePairsAlive H X S) :
    ∀ e ∈ outsideLiveUncoveredEdges H X S,
      d ≤ (greedyChoicesCoveringEdge S e).card := by
  intro e he
  have heTrack : e ∈ outsideTrackablePart H X
      (greedyUncoveredEdges
        (graphEdges (SimpleGraph.completeGraph V)) S) := he
  have heUncovered : e ∈ greedyUncoveredEdges
      (graphEdges (SimpleGraph.completeGraph V)) S :=
    outsideTrackablePart_subset H X _ heTrack
  have hoff : ¬ e.IsDiag :=
    outsideTrackablePart_offdiag H X _ e heTrack
  rw [card_greedyChoicesCoveringEdge_eq_availablePair S e hoff]
  exact hfloor e.toFinset (Sym2.card_toFinset_of_not_isDiag e hoff)
    (availablePair_nonempty_of_trackable_uncovered
      houtside e heTrack heUncovered)

/-- Summing the live pair-star floor gives a deterministic lower bound for
the number of available triples. -/
theorem outsideLiveUncoveredEdges_card_mul_div_three_le_available
    {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {X : Finset V} {S : GreedyStateOn V} {d : ℕ}
    (hfloor : HasAvailablePairFloor d S)
    (houtside : OutsideLeavePairsAlive H X S) :
    (outsideLiveUncoveredEdges H X S).card * d / 3 ≤ S.available.card := by
  have hcover := card_mul_div_three_le_greedyCoveringChoices S
    (outsideLiveUncoveredEdges H X S) d
    (outsideLiveUncoveredEdges_pairSupply hfloor houtside)
  calc
    (outsideLiveUncoveredEdges H X S).card * d / 3 ≤
        (greedyCoveringChoices S
          (outsideLiveUncoveredEdges H X S)).card := hcover
    _ ≤ (univ : Finset S.available).card := card_le_card (subset_univ _)
    _ = S.available.card := by simp

/-- A convenient scheduled form: it is enough to provide a lower bound on
the number of eligible uncovered pairs. -/
theorem scheduled_available_floor_of_outside_pairs
    {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {X : Finset V} {S : GreedyStateOn V}
    {R d D : ℕ}
    (hfloor : HasAvailablePairFloor d S)
    (houtside : OutsideLeavePairsAlive H X S)
    (hR : R ≤ (outsideLiveUncoveredEdges H X S).card)
    (hD : D ≤ R * d / 3) :
    D ≤ S.available.card := by
  exact hD.trans ((Nat.div_le_div_right (Nat.mul_le_mul_right d hR)).trans
    (outsideLiveUncoveredEdges_card_mul_div_three_le_available
      hfloor houtside))

/-- Clock-synchronized form used by the sharp stopped process. -/
theorem scheduled_available_floor_of_clock
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {H : SimpleGraph V} {X : Finset V}
    {S₀ S : GreedyStateOn V} {i d D : ℕ}
    (htraj : PairTrajectoryInvariant F S₀ S)
    (hchosen₀ : S₀.chosen = ∅)
    (hcard : S.chosen.card = S₀.chosen.card + i)
    (hfloor : HasAvailablePairFloor d S)
    (houtside : OutsideLeavePairsAlive H X S)
    (hD : D ≤
      (Nat.choose (Fintype.card V) 2 - 3 * i -
          (graphEdges H).card - X.sym2.card) * d / 3) :
    D ≤ S.available.card := by
  have hR := choose_sub_chosen_sub_exceptions_le_outsideLiveUncoveredEdges_card
    H X S htraj.1.1
  rw [hcard, hchosen₀] at hR
  simp only [card_empty, zero_add] at hR
  exact scheduled_available_floor_of_outside_pairs hfloor houtside hR hD

end

end Erdos207
