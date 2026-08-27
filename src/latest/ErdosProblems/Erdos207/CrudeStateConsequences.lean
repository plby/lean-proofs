/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CrudeStatisticIndex
import ErdosProblems.Erdos207.PairThreatIntersectionCount
import ErdosProblems.Erdos207.ClosedThreatTrajectoryError

/-! # Deterministic drift inputs supplied by the simultaneous crude event -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def crudeOrderIndexOfBudget {q d : ℕ} (j c : ℕ) (hj : j ≤ q) (hc : c + d ≤ j) :
    CrudeOrderIndex q d := ⟨(⟨j, by omega⟩, ⟨c, by omega⟩), hc⟩

namespace CrudeStateBounds

variable {V : Type*} [Fintype V] [DecidableEq V]
  {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q : ℕ} {K : CrudeThresholds}

theorem rooted (h : CrudeStateBounds F S q K) (j c : ℕ) (T U : TripleOn V)
    (hj : j ≤ q) (hc : c + 5 ≤ j) (hne : T ≠ U) :
    ((greedyRootedConfigurationClass (forbiddenFamilyOfOrder F j) S {T, U} c).card : ℝ≥0) <
      K.rooted j c :=
  h (.inl (crudeOrderIndexOfBudget j c hj hc, ⟨(T, U), hne⟩))

theorem pair (h : CrudeStateBounds F S q K) (T : TripleOn V) (P : PairOn V) :
    selectedCount (fun w : PairTwoAwayThreatWitness V F T P ↦ pairTwoAwayThreatRemainder w)
      S.chosen < K.pair := h (.inr (.inl (T, P)))

theorem common (h : CrudeStateBounds F S q K) (T T' : TripleOn V) :
    selectedCount (fun w : CommonThreatWitness F F T T' ↦ w.remainder) S.chosen < K.common :=
  h (.inr (.inr (.inl (T, T'))))

theorem gain (h : CrudeStateBounds F S q K) (j c : ℕ) (T : TripleOn V)
    (hj : j ≤ q) (hc : c + 4 ≤ j) :
    (greedyActiveGainDefectCount (forbiddenFamilyOfOrder F j) F S T c : ℝ≥0) < K.gain j c :=
  h (.inr (.inr (.inr (crudeOrderIndexOfBudget j c hj hc, T))))

theorem closed_inter (h : CrudeStateBounds F S q K)
    (hS : GreedyInvariant F S) (hpack : ∀ E ∈ F, IsPackingOn E)
    {T T' : TripleOn V} (hT : T ∈ S.available) (hT' : T' ∈ S.available)
    (hdis : (T.1 ∩ T'.1).card ≤ 1) :
    ((greedyClosedThreats F S T ∩ greedyClosedThreats F S T').card : ℝ≥0) ≤
      9 + 6 * K.pair + K.common := by
  have hb := card_closedThreats_inter_le_crude_cutoffs hS hT hT' hdis hpack
    K.pair K.pair K.common (fun p ↦ (h.pair T' p.1).le) (fun p ↦ (h.pair T p.1).le)
    (h.common T T').le
  convert hb using 1 <;> ring

theorem pair_inter (h : CrudeStateBounds F S q K) (P : PairOn V) (T : TripleOn V)
    (hPT : ¬ P.1 ⊆ T.1) (hpack : ∀ E ∈ F, IsPackingOn E) :
    ((availableTrianglesContainingPair S P.1 ∩ greedyClosedThreats F S T).card : ℝ≥0) ≤
      3 + K.pair :=
  (card_pairStar_inter_closedThreats_le_selected F S P T hPT hpack).trans
    (add_le_add le_rfl (h.pair T P).le)

theorem terminal_loss (h : CrudeStateBounds F S q K)
    (hS : GreedyInvariant F S) (hpack : ∀ E ∈ F, IsPackingOn E)
    {root T : TripleOn V} (hroot : root ∈ S.available)
    (hT : T ∈ S.available \ greedyClosedThreats F S root)
    (j : ℕ) (hj : 4 ≤ j) :
    ((greedyConfigurationLosses F (forbiddenFamilyOfOrder F j) S root (j - 4) T).card : ℝ≥0) ≤
      3 * K.pair + K.common := by
  apply terminal_configuration_losses_card_le_moment_cutoffs hS hroot hT
    (fun E hE ↦ (mem_forbiddenFamilyOfOrder.mp hE).1)
    (fun E hE ↦ hpack E (mem_forbiddenFamilyOfOrder.mp hE).1) ?_ K.pair K.common
    (fun p ↦ (h.pair root p.1).le) (h.common root T).le
  intro E hE
  have hc := (mem_forbiddenFamilyOfOrder.mp hE).2
  omega

theorem threat_trajectory (h : CrudeStateBounds F S q K)
    (hS : GreedyInvariant F S) (hpack : ∀ E ∈ F, IsPackingOn E)
    (hcard : ∀ E ∈ F, 2 ≤ E.card → E.card + 2 ≤ q)
    {T : TripleOn V} (hT : T ∈ S.available)
    (x ex : ℝ) (y ey : ℕ → ℝ)
    (hpair : ∀ P ∈ T.1.powersetCard 2,
      |((availableTrianglesContainingPair S P).card : ℝ) - x| ≤ ex)
    (hterminal : ∀ j ∈ Icc 4 q,
      |((greedyConfigurationClass (forbiddenFamilyOfOrder F j) S T (j - 4)).card : ℝ) - y j| ≤ ey j) :
    |((greedyClosedThreats F S T).card : ℝ) - (3 * x + (∑ j ∈ Icc 4 q, y j) - 2)| ≤
      (K.common : ℝ) + 3 * ex + ∑ j ∈ Icc 4 q, ey j := by
  exact abs_greedyClosedThreats_sub_trajectory_le hS hT hpack hcard x ex K.common y ey hpair hterminal
    (by exact_mod_cast (h.common T T).le)

end CrudeStateBounds

theorem sum_redundantWitnesses_le_of_crude_minimal
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (q : ℕ) (K : CrudeThresholds)
    (h : CrudeStateBounds (minimalForbiddenFamily F) S q K)
    (j c : ℕ) {T : TripleOn V} (hT : T ∈ S.available) (hj : j ≤ q) (hc : c + 4 ≤ j) :
    (∑ E ∈ greedyConfigurationClass (forbiddenFamilyOfOrder (minimalForbiddenFamily F) j) S T c,
      ((greedyConfigurationRedundantWitnesses (minimalForbiddenFamily F) S E).card : ℝ≥0)) ≤
        K.gain j c := by
  have hsum := card_greedyGainDefectPairs_minimal_eq_sum F
    (forbiddenFamilyOfOrder (minimalForbiddenFamily F) j) S T c
    (fun E hE ↦ (mem_forbiddenFamilyOfOrder.mp hE).1)
  have hg := (h.gain j c T hj hc).le
  simp only [greedyActiveGainDefectCount, if_pos hT, hsum, Nat.cast_sum] at hg
  exact hg

end

end Erdos207
