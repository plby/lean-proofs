/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointEligibility
import ErdosProblems.Erdos599.CarrierHammockCoherent

/-!
# Actual prefix-causal native endpoint hammock tracking

This instantiates the representation-independent recursion with the proved
increasing native route eligibility. Its cap is the ladder's index cardinal;
in the halfway application both are the successor of kappa. All definitions
inspect only current and earlier stage warps and frontiers. No final-owner
or limiting-hammock choice occurs in the row selector.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeEndpointTracker

open Set Cardinal Order Ladder ColouredSafeTrace
open DWeb.KappaLadder.Deferred ColouredSafeEndpointEligibility

universe u

variable {V : Type u} {Gamma : DWeb V} {rho : Cardinal.{u}}
variable (L : Gamma.KappaLadder rho) (s : V) (e : Option V) (strong : Bool)

def selectedAt (a : Stage rho) : Set (Trace V) :=
  CarrierHammock.Coherent.chosenAt (fun b ↦ goodAt L b s e strong)
    Trace.vertexSet (ColouredSafeHammock.endpoints s e) a

def selectedCarrierAt (a : Stage rho) : Set V :=
  ⋃ q : selectedAt L s e strong a, q.1.vertexSet

theorem selectedAt_card_le (hrho : aleph0 ≤ rho) (a : Stage rho) :
    #(selectedAt L s e strong a) ≤ rho :=
  CarrierHammock.Coherent.chosenAt_card_le _ _ _ hrho a

theorem selectedCarrierAt_card_le (hrho : aleph0 ≤ rho) (a : Stage rho) :
    #(selectedCarrierAt L s e strong a) ≤ rho :=
  CarrierHammock.mk_carrierUnion_le hrho (selectedAt_card_le L s e strong hrho a)
    (fun q _ ↦ q.vertexSet_countable)

/-- Prefix geometry alone determines the selected row, even for the
arbitrary truncated ladders on which a causal rule is evaluated. -/
theorem selectedAt_congr_le (L' : Gamma.KappaLadder rho) (a : Stage rho)
    (hprefix : ∀ b, b ≤ a →
      L.warpAt b = L'.warpAt b ∧ L.frontier b = L'.frontier b) :
    selectedAt L s e strong a = selectedAt L' s e strong a := by
  apply CarrierHammock.Coherent.chosenAt_congr_le
  intro b hba
  dsimp only [goodAt]
  rw [(hprefix b hba).1, (hprefix b hba).2]

theorem selectedAt_spec (hrho : aleph0 ≤ rho) (hL : HalfwayGeometry L)
    (a : Stage rho) :
    MaximalUpTo
      {J | CarrierHammock.Admissible (goodAt L a s e strong) Trace.vertexSet
        (ColouredSafeHammock.endpoints s e) J} rho (selectedAt L s e strong a) :=
  (CarrierHammock.Coherent.chosenAt_spec _ _ _ hrho (goodAt_monotone hL) a).1

theorem selectedAt_monotone (hrho : aleph0 ≤ rho) (hL : HalfwayGeometry L) :
    Monotone (selectedAt L s e strong) :=
  CarrierHammock.Coherent.chosenAt_monotone _ _ _ hrho (goodAt_monotone hL)

theorem selectedCarrierAt_subset_roof (hrho : aleph0 ≤ rho) (hL : HalfwayGeometry L)
    (a : Stage rho) : selectedCarrierAt L s e strong a ⊆ Gamma.roof (L.frontier a) := by
  intro x hx
  obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hx
  have hgood := (selectedAt_spec L s e strong hrho hL a).mem.1 q.2
  obtain ⟨A, hA, hAq⟩ := hgood
  rw [← hAq, ofOccurrence_vertexSet] at hxq
  exact hA.2.2.2.2.1 hxq

def total : Set (Trace V) := ⋃ a : Stage rho, selectedAt L s e strong a

/-- A maximal-up-to family of actual captured traces comes from the union
of causal rows; it is not selected independently after the ladder is fixed. -/
theorem total_maximalUpTo (hrho : aleph0 ≤ rho) (hL : HalfwayGeometry L) :
    MaximalUpTo
      {J | CarrierHammock.Admissible (captured L s e strong) Trace.vertexSet
        (ColouredSafeHammock.endpoints s e) J} rho (total L s e strong) := by
  have h := CarrierHammock.Coherent.total_maximalUpTo
    (fun a ↦ goodAt L a s e strong) Trace.vertexSet
    (ColouredSafeHammock.endpoints s e) hrho (goodAt_monotone hL)
  rw [iUnion_goodAt_eq_captured hL] at h
  exact h

/-- Endpoint requests may start late: monotonicity makes every earlier
selected route available in every sufficiently late row. -/
theorem total_carrier_subset_of_eventually
    (hrho : aleph0 ≤ rho) (hL : HalfwayGeometry L) (d : Stage rho)
    {Z : Set V}
    (hZ : ∀ a, d ≤ a → selectedCarrierAt L s e strong a ⊆ Z) :
    ∀ q ∈ total L s e strong, q.vertexSet ⊆ Z := by
  intro q hq x hx
  obtain ⟨a, hqa⟩ := Set.mem_iUnion.mp hq
  have hqb := selectedAt_monotone L s e strong hrho hL (le_max_left a d) hqa
  apply hZ (max a d) (le_max_right a d)
  exact Set.mem_iUnion.mpr ⟨⟨q, hqb⟩, hx⟩

/-- All endpoint requests born in one small carrier, with both filter flags. -/
def requestedCarriers (a : Stage rho) (X : Set V) : Set V :=
  ⋃ s : X,
    (selectedCarrierAt L s.1 none false a ∪ selectedCarrierAt L s.1 none true a) ∪
      ⋃ t : X, selectedCarrierAt L s.1 (some t.1) false a ∪
        selectedCarrierAt L s.1 (some t.1) true a

theorem requestedCarriers_card_le (hrho : aleph0 ≤ rho)
    (a : Stage rho) {X : Set V} (hX : #X ≤ rho) :
    #(requestedCarriers L a X) ≤ rho := by
  unfold requestedCarriers
  apply (Cardinal.mk_iUnion_le _).trans
  apply Cardinal.mul_le_of_le hrho hX
  apply ciSup_le'
  intro s
  apply (Cardinal.mk_union_le _ _).trans
  apply Cardinal.add_le_of_le hrho
  · exact (Cardinal.mk_union_le _ _).trans
      (Cardinal.add_le_of_le hrho
        (selectedCarrierAt_card_le L s.1 none false hrho a)
        (selectedCarrierAt_card_le L s.1 none true hrho a))
  · apply (Cardinal.mk_iUnion_le _).trans
    apply Cardinal.mul_le_of_le hrho hX
    apply ciSup_le'
    intro t
    exact (Cardinal.mk_union_le _ _).trans
      (Cardinal.add_le_of_le hrho
        (selectedCarrierAt_card_le L s.1 (some t.1) false hrho a)
        (selectedCarrierAt_card_le L s.1 (some t.1) true hrho a))

theorem selectedCarrierAt_subset_requestedCarriers
    (a : Stage rho) {X : Set V} (hs : s ∈ X) (he : ∀ t, e = some t → t ∈ X) :
    selectedCarrierAt L s e strong a ⊆ requestedCarriers L a X := by
  intro x hx
  refine Set.mem_iUnion.mpr ⟨⟨s, hs⟩, ?_⟩
  cases e with
  | none =>
      apply Or.inl
      cases strong with
      | false => exact Or.inl hx
      | true => exact Or.inr hx
  | some t =>
      apply Or.inr
      refine Set.mem_iUnion.mpr ⟨⟨t, he t rfl⟩, ?_⟩
      cases strong with
      | false => exact Or.inl hx
      | true => exact Or.inr hx

#print axioms selectedAt_congr_le
#print axioms selectedAt_spec
#print axioms selectedCarrierAt_subset_roof
#print axioms total_maximalUpTo
#print axioms total_carrier_subset_of_eventually
#print axioms requestedCarriers_card_le
#print axioms selectedCarrierAt_subset_requestedCarriers

end Erdos599.Blueprint.ColouredSafeEndpointTracker
