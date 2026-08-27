/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ThreatIntersectionWitnesses
import ErdosProblems.Erdos207.PairSharingIntersection

/-! # Explicit bounds for common closed threats -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem card_closedThreats_inter_le_crude_cutoffs
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {T T' : TripleOn V}
    (hS : GreedyInvariant F S) (hT : T ∈ S.available) (hT' : T' ∈ S.available)
    (hdis : (T.1 ∩ T'.1).card ≤ 1) (hpack : ∀ E ∈ F, IsPackingOn E)
    (P P' Q : ℝ≥0)
    (hP : ∀ p : PairInsideSelector T, selectedCount
      (fun w : PairTwoAwayThreatWitness V F T' p.1 ↦ pairTwoAwayThreatRemainder w) S.chosen ≤ P)
    (hP' : ∀ p : PairInsideSelector T', selectedCount
      (fun w : PairTwoAwayThreatWitness V F T p.1 ↦ pairTwoAwayThreatRemainder w) S.chosen ≤ P')
    (hQ : selectedCount (fun w : CommonThreatWitness F F T T' ↦ w.remainder) S.chosen ≤ Q) :
    ((greedyClosedThreats F S T ∩ greedyClosedThreats F S T').card : ℝ≥0) ≤
      9 + 3 * P + 3 * P' + Q := by
  have hne : T ≠ T' := by
    intro h
    rw [h, inter_self, T'.2] at hdis
    omega
  let A := triplesSharingPair T ∩ triplesSharingPair T'
  let B := pairLocalThreatUnion F S.chosen T' T
  let C := pairLocalThreatUnion F S.chosen T T'
  let D := selectedWitnessImage (fun w : CommonThreatWitness F F T T' ↦ w.remainder)
    (fun w ↦ w.bridge) S.chosen
  have hsub : greedyClosedThreats F S T ∩ greedyClosedThreats F S T' ⊆ (A ∪ B) ∪ (C ∪ D) :=
    closedThreats_inter_subset_witness_union hS hT hT' hne hpack
  have hnat : (greedyClosedThreats F S T ∩ greedyClosedThreats F S T').card ≤
      (A.card + B.card) + (C.card + D.card) :=
    (card_le_card hsub).trans ((card_union_le (A ∪ B) (C ∪ D)).trans
      (Nat.add_le_add (card_union_le A B) (card_union_le C D)))
  have ha : (A.card : ℝ≥0) ≤ 9 := by exact_mod_cast card_pairSharing_inter_le_nine hdis
  have hb : (B.card : ℝ≥0) ≤ 3 * P := card_pairLocalThreatUnion_le_three_mul F S.chosen T' T P hP
  have hc : (C.card : ℝ≥0) ≤ 3 * P' := card_pairLocalThreatUnion_le_three_mul F S.chosen T T' P' hP'
  have hd : (D.card : ℝ≥0) ≤ Q :=
    (card_selectedWitnessImage_le_selectedCount _ _ S.chosen).trans hQ
  calc
    _ ≤ ((A.card : ℝ≥0) + B.card) + ((C.card : ℝ≥0) + D.card) := by exact_mod_cast hnat
    _ ≤ (9 + 3 * P) + (3 * P' + Q) := add_le_add (add_le_add ha hb) (add_le_add hc hd)
    _ = _ := by ring

end

end Erdos207
