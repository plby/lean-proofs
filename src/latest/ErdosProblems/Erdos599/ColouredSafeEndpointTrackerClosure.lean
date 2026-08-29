/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointTracker
import ErdosProblems.Erdos599.CarrierHammockEmbedding
import ErdosProblems.Erdos599.ColouredSafeEndpointHammockClosure

/-!
# Decoding the causal trace tracker to native endpoint closure

The captured trace class is exactly the injective image of genuinely valid
captured native occurrences. Pulling the actual coherent union back along
that encoding preserves its maximal-up-to property and its carrier. This
provides the closure predicate consumed by the endpoint blueprint modules,
not merely a parallel trace-level surrogate.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeEndpointTracker

open Set Cardinal Order Ladder ColouredSafeTrace
open DWeb.KappaLadder.Deferred ColouredSafeEndpointEligibility
open ColouredSafeAmbientOccurrence ColouredSafeEndpointReference ColouredSafeHammock

universe u

variable {V : Type u} {Gamma : DWeb V} {rho : Cardinal.{u}}
variable (L : Gamma.KappaLadder rho) (s : V) (e : Option V) (strong : Bool)

theorem captured_eq_image_native :
    captured L s e strong = ofOccurrence ''
      goodRoutes (reference L.limitWarp s e) s e
        (fun A ↦ ColouredSafeEndpointHammock.CapturedByStageRoof L s e A ∧
          NondegenerateWhen strong e A) := by
  ext q
  constructor
  · intro hq
    obtain ⟨a, A, hA, rfl⟩ := Set.mem_iUnion.mp hq
    rcases hA with ⟨hv, he, hs, ht, hroof, hflag⟩
    exact ⟨A, ⟨hv, he, hs, ht, ⟨a, hroof⟩, hflag⟩, rfl⟩
  · rintro ⟨A, hA, rfl⟩
    rcases hA with ⟨hv, he, hs, ht, ⟨a, hroof⟩, hflag⟩
    exact Set.mem_iUnion.mpr ⟨a, A, ⟨hv, he, hs, ht, hroof, hflag⟩, rfl⟩

theorem closedAt_of_eventual_carrier
    (hrho : aleph0 ≤ rho) (hL : HalfwayGeometry L) (d : Stage rho)
    {Z : Set V} (hZ : ∀ a, d ≤ a → selectedCarrierAt L s e strong a ⊆ Z) :
    ClosedAt (reference L.limitWarp s e) s e
      (fun A ↦ ColouredSafeEndpointHammock.CapturedByStageRoof L s e A ∧
        NondegenerateWhen strong e A) rho Z := by
  let good := goodRoutes (reference L.limitWarp s e) s e
    (fun A ↦ ColouredSafeEndpointHammock.CapturedByStageRoof L s e A ∧
      NondegenerateWhen strong e A)
  let H := total L s e strong
  have hH := total_maximalUpTo L s e strong hrho hL
  rw [captured_eq_image_native] at hH
  have hPull := CarrierHammock.maximalUpTo_encodedPullback
    (ofOccurrence_injective (Y := reference L.limitWarp s e) (s := s)) hH
  let K := CarrierHammock.encodedPullback ofOccurrence good H
  refine ⟨K, ?_, ?_⟩
  · simpa only [ColouredSafeHammock.Hammock, ofOccurrence_vertexSet] using hPull
  · intro A hA
    have hcarrier := total_carrier_subset_of_eventually L s e strong hrho hL d hZ
      (ofOccurrence A) hA.2
    simpa only [ofOccurrence_vertexSet] using hcarrier

theorem ordinary_closedAt_of_eventual_carrier
    (hrho : aleph0 ≤ rho) (hL : HalfwayGeometry L) (d : Stage rho)
    {Z : Set V} (hZ : ∀ a, d ≤ a → selectedCarrierAt L s e false a ⊆ Z) :
    ClosedAt (reference L.limitWarp s e) s e
      (ColouredSafeEndpointHammock.CapturedByStageRoof L s e) rho Z := by
  simpa [NondegenerateWhen] using closedAt_of_eventual_carrier L s e false hrho hL d hZ

theorem nondegenerate_closedAt_of_eventual_carrier (t : V)
    (hrho : aleph0 ≤ rho) (hL : HalfwayGeometry L) (d : Stage rho)
    {Z : Set V} (hZ : ∀ a, d ≤ a → selectedCarrierAt L s (some t) true a ⊆ Z) :
    ClosedAt (reference L.limitWarp s (some t)) s (some t)
      (fun A ↦ ColouredSafeEndpointHammock.CapturedByStageRoof L s (some t) A ∧
        ¬A.HasFiniteSwitchedPathTo t) rho Z := by
  simpa [NondegenerateWhen] using
    closedAt_of_eventual_carrier L s (some t) true hrho hL d hZ

#print axioms captured_eq_image_native
#print axioms closedAt_of_eventual_carrier
#print axioms ordinary_closedAt_of_eventual_carrier
#print axioms nondegenerate_closedAt_of_eventual_carrier

end Erdos599.Blueprint.ColouredSafeEndpointTracker
