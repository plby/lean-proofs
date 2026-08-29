/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointContainedClosure
import ErdosProblems.Erdos599.ColouredSafeEndpointClosedCarrier

/-!
# Full-reference closure from endpoint-indexed closure

If a displayed endpoint is covered by the full reference, no exposed good
route exists. Otherwise pruning endpoint owners leaves the reference exactly
unchanged. Thus the same small contained carrier has all three closure
certificates needed by the native moving construction.
-/

noncomputable section

namespace Erdos599.Blueprint

open Set Cardinal Order DirectedPath Ladder LinkageBlueprint
open ColouredSafeAmbientOccurrence ColouredSafeHammock
open ColouredSafeEndpointReference ColouredSafeHammockOmegaClosure

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}

namespace ColouredSafeHammock

theorem closedAt_of_no_good {s : V} {e : Option V} {extra : Occurrence Y s → Prop}
    {rho : Cardinal.{u}} {X : Set V}
    (hno : ∀ A, A ∉ goodRoutes Y s e extra) : ClosedAt Y s e extra rho X := by
  have hEmpty : ColouredSafeHammock.Hammock Y s e extra ∅ := CarrierHammock.empty_admissible
  refine ⟨∅, maximalUpTo_of_maximal hEmpty ?_ (by simp), by simp⟩
  refine ⟨hEmpty, ?_⟩
  intro K hK _ A hA
  exact (hno A (hK.1 hA)).elim

end ColouredSafeHammock

namespace ColouredSafeEndpointReference

theorem reference_eq_of_endpoints_off {s : V} {e : Option V}
    (hs : s ∉ Gamma.vertexSet Y)
    (ht : ∀ t, e = some t → t ∉ Gamma.vertexSet Y) : reference Y s e = Y := by
  apply Set.Subset.antisymm reference_subset
  intro p hp
  refine ⟨hp, Set.disjoint_left.mpr ?_⟩
  intro x hxp hx
  rcases hx with hx | hx
  · have hxs : x = s := hx
    exact hs ⟨p, hp, hxs ▸ hxp⟩
  · exact ht x hx ⟨p, hp, hxp⟩

end ColouredSafeEndpointReference

namespace ColouredSafeEndpointHammock

theorem Closed.captured_fullReference {kappa rho : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {X : Set V}
    (hX : Closed L.limitWarp (CapturedByStageRoof L) rho X) :
    FilteredOmegaClosed L.limitWarp (ColouredSafeHammock.CapturedByStageRoof L) rho X := by
  have hpair : ∀ s e, endpoints s e ⊆ X →
      ClosedAt L.limitWarp s e (ColouredSafeHammock.CapturedByStageRoof L s) rho X ∧
        ∀ t, e = some t → ClosedAt L.limitWarp s e
          (fun A ↦ ColouredSafeHammock.CapturedByStageRoof L s A ∧
            ¬A.HasFiniteSwitchedPathTo t) rho X := by
    intro s e hends
    by_cases hs : s ∉ Gamma.vertexSet L.limitWarp
    · by_cases ht : ∀ t, e = some t → t ∉ Gamma.vertexSet L.limitWarp
      · have hRef := reference_eq_of_endpoints_off hs ht
        obtain ⟨hO, hN⟩ := hX s e hends
        change ClosedAt (reference L.limitWarp s e) s e
          (fun A ↦ ∃ a : Stage kappa, A.vertexSet ⊆ Gamma.roof (L.frontier a)) rho X at hO
        change (∀ t, e = some t → ClosedAt (reference L.limitWarp s e) s e
          (fun A ↦ (∃ a : Stage kappa, A.vertexSet ⊆ Gamma.roof (L.frontier a)) ∧
            ¬A.HasFiniteSwitchedPathTo t) rho X) at hN
        rw [hRef] at hO hN
        exact ⟨hO, hN⟩
      · constructor
        · exact closedAt_of_no_good (fun _ hA ↦ ht hA.2.2.2.1)
        · intro t _
          exact closedAt_of_no_good (fun _ hA ↦ ht hA.2.2.2.1)
    · constructor
      · exact closedAt_of_no_good (fun _ hA ↦ hs hA.2.2.1)
      · intro t _
        exact closedAt_of_no_good (fun _ hA ↦ hs hA.2.2.1)
  constructor
  · intro s hs
    exact (hpair s none (by simpa using hs)).1
  · intro s hs t ht
    have h := hpair s (some t) (by
      rw [endpoints_some, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨hs, ht⟩)
    exact ⟨h.1, h.2 t rfl⟩

end ColouredSafeEndpointHammock

namespace ColouredSafeEndpointBlueprint.ClosedCarrier

variable {kappa : Cardinal.{u}} {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {Z seed : Set V}

/-- The existing closed causal carrier supplies the full moving-interface
closure on a genuinely contained small superset of the seed. -/
theorem exists_small_jointClosed_within (hZ : ColouredSafeEndpointBlueprint.ClosedCarrier C Z)
    (hcard : #seed ≤ kappa) (hseed : seed ⊆ Z) :
    ∃ X : Set V, seed ⊆ X ∧ #X ≤ kappa ∧ X ⊆ Z ∧
      FilteredOmegaClosed C.ladder.limitWarp
        (ColouredSafeHammock.CapturedByStageRoof C.ladder) kappa X ∧
      ClosedUnderPaths Gamma C.ladder.limitWarp X ∧
      ColouredSafeEndpointHammock.Closed C.ladder.limitWarp
        (ColouredSafeEndpointHammock.CapturedByStageRoof C.ladder) kappa X := by
  obtain ⟨X, hseedX, hXcard, hXZ, hXclosed, hXref⟩ :=
    hZ.endpoint_closed.exists_small_jointClosed_within C.capacity_infinite
      (C.legal.warpStages (Ladder.finalStage (succ kappa))) hZ.reference_closed hcard hseed
  exact ⟨X, hseedX, hXcard, hXZ, hXclosed.captured_fullReference, hXref, hXclosed⟩

end ColouredSafeEndpointBlueprint.ClosedCarrier

#print axioms ColouredSafeHammock.closedAt_of_no_good
#print axioms ColouredSafeEndpointReference.reference_eq_of_endpoints_off
#print axioms ColouredSafeEndpointHammock.Closed.captured_fullReference
#print axioms ColouredSafeEndpointBlueprint.ClosedCarrier.exists_small_jointClosed_within

end Erdos599.Blueprint
