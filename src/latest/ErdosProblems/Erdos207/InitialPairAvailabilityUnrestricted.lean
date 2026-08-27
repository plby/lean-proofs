/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialPairAvailability

/-! # Initial pair availability without an unnecessary bank-pair support hypothesis -/

namespace Erdos207

open Finset

noncomputable section

theorem card_thirdVertex_le_initialLegal_add_losses
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} [DecidableRel H.Adj] {bank : TripleSystemOn V}
    {u v : V} (huv : u ≠ v) (hnotH : ¬ H.Adj u v) :
    Fintype.card (ThirdVertex u v) ≤
      (legalThirdVertices (absorberErdosForbiddenConfigurationsOn q bank)
        (outsideAvailableTriangles H bank) ∅ huv).card +
      (H.degree u + H.degree v + (verticesOn bank).card) := by
  let L := legalThirdVertices (absorberErdosForbiddenConfigurationsOn q bank) (outsideAvailableTriangles H bank) ∅ huv
  let E := absorberEdgeBlockedThirdVertices H huv
  let K := bankSupportThirdVertices bank huv
  have hcover : (univ : Finset (ThirdVertex u v)) ⊆ L ∪ (E ∪ K) := by
    intro w _
    by_cases hL : w ∈ L
    · exact mem_union_left _ hL
    · exact mem_union_right _ (initial_illegal_third_subset_edge_union_bankSupport
        huv (mem_sdiff.mpr ⟨mem_univ _, hL⟩))
  have hE := card_absorberEdgeBlockedThirdVertices_le_degree_add (H := H) huv hnotH
  have hK := card_bankSupportThirdVertices_le (B := bank) huv
  calc
    _ = (univ : Finset (ThirdVertex u v)).card := by simp
    _ ≤ (L ∪ (E ∪ K)).card := card_le_card hcover
    _ ≤ L.card + (E ∪ K).card := card_union_le _ _
    _ ≤ L.card + (E.card + K.card) := Nat.add_le_add_left (card_union_le _ _) _
    _ ≤ _ := Nat.add_le_add_left (Nat.add_le_add hE hK) _

theorem card_sub_two_le_initialPairStar_add_three_mul_unrestricted
    {V : Type*} [Fintype V] [DecidableEq V]
    {q C : ℕ} {H : SimpleGraph V} [DecidableRel H.Adj] {bank : TripleSystemOn V}
    (hdegree : ∀ x, H.degree x ≤ C) (hsupport : (verticesOn bank).card ≤ C)
    {u v : V} (huv : u ≠ v) (hnotH : ¬ H.Adj u v) :
    Fintype.card V - 2 ≤ (availableTrianglesContainingPair (absorberGreedyInitialState
      (absorberErdosForbiddenConfigurationsOn q bank) (outsideAvailableTriangles H bank)) {u, v}).card + 3 * C := by
  have hraw := card_thirdVertex_le_initialLegal_add_losses (q := q) (bank := bank) huv hnotH
  have hinj := card_initialLegalThirdVertices_le_pairStar (absorberErdosForbiddenConfigurationsOn q bank)
    (outsideAvailableTriangles H bank) huv
  rw [card_thirdVertex huv] at hraw
  have hu := hdegree u
  have hv := hdegree v
  omega

end

end Erdos207
