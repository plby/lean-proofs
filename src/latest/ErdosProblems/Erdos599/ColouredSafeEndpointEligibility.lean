/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeTrace

/-!
# Increasing, stage-local eligibility of native endpoint traces

Eligibility is defined using only the current stage reference and roof.
Every eligible word already captures its own endpoints. The checked
identification and two-way transport therefore prove that stage eligibility
is precisely global-reference eligibility within that stage roof. Both the
ordinary and finite nondegenerate filters are preserved, and eligibility
is monotone on an actual deferred ladder.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeEndpointEligibility

open Set Cardinal DirectedPath Alternating Ladder
open DWeb.KappaLadder.Deferred ColouredSafeAmbientOccurrence
open ColouredSafeReverseReachability ColouredSafeTrace
open ColouredSafeEndpointReference ColouredSafeEndpointStageReference

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {s : V} {e : Option V} {strong : Bool} {R S : Set V}

/-- The ordinary flag adds no condition. The strong flag excludes finite
switched reachability to the specified endpoint; it is vacuous for infinity. -/
def NondegenerateWhen (strong : Bool) (e : Option V) (A : Occurrence Y s) : Prop :=
  ∀ t, e = some t → strong = true → ¬A.HasFiniteSwitchedPathTo t

def goodTraces (Y : Set Gamma.DPath) (s : V) (e : Option V)
    (strong : Bool) (R : Set V) : Set (Trace V) :=
  ofOccurrence '' ColouredSafeHammock.goodRoutes Y s e
    (fun A ↦ A.vertexSet ⊆ R ∧ NondegenerateWhen strong e A)

theorem goodTraces_mono_region (hRS : R ⊆ S) :
    goodTraces Y s e strong R ⊆ goodTraces Y s e strong S := by
  rintro q ⟨A, hA, rfl⟩
  rcases hA with ⟨hvalid, hend, hs, ht, hR, hstrong⟩
  exact ⟨A, ⟨hvalid, hend, hs, ht, hR.trans hRS, hstrong⟩, rfl⟩

theorem endpoints_subset_region {q : Trace V}
    (hq : q ∈ goodTraces Y s e strong R) : ColouredSafeHammock.endpoints s e ⊆ R := by
  obtain ⟨A, hA, _⟩ := hq
  rcases hA with ⟨_, hend, _, _, hR, _⟩
  rintro x (hxs | hxend)
  · exact hxs ▸ hR A.source_mem_vertexSet
  · exact hR (A.terminal_mem_vertexSet (hend.trans hxend))

variable {kappa : Cardinal.{u}} {L : Gamma.KappaLadder kappa} {a : Stage kappa}

theorem goodTraces_promote (hL : HalfwayGeometry L) :
    goodTraces (stageReference hL a s e) s e strong (Gamma.roof (L.frontier a)) ⊆
      goodTraces (reference L.limitWarp s e) s e strong (Gamma.roof (L.frontier a)) := by
  rintro q ⟨A, hA, rfl⟩
  rcases hA with ⟨hvalid, hend, _hs, _ht, hRoof, hstrong⟩
  refine ⟨A.retypeEndpointLimitReference hL hRoof, ?_, by simp only [ofOccurrence_promote]⟩
  refine ⟨hvalid.retypeEndpointLimitReference hL hRoof, ?_, source_off, ?_, ?_, ?_⟩
  · simpa only [CurrentSafeOccurrence.retypeEndpointLimitReference_terminal?] using hend
  · intro t ht
    exact terminal_off ht
  · simpa only [CurrentSafeOccurrence.retypeEndpointLimitReference_vertexSet] using hRoof
  · intro t het hflag hdeg
    exact hstrong t het hflag
      ((A.hasFiniteSwitchedPathTo_retypeEndpointLimitReference_iff hL hRoof
        (hRoof (A.terminal_mem_vertexSet (hend.trans het)))).mp hdeg)

theorem goodTraces_localize (hL : HalfwayGeometry L) :
    goodTraces (reference L.limitWarp s e) s e strong (Gamma.roof (L.frontier a)) ⊆
      goodTraces (stageReference hL a s e) s e strong (Gamma.roof (L.frontier a)) := by
  rintro q ⟨A, hA, rfl⟩
  rcases hA with ⟨hvalid, hend, _hs, _ht, hRoof, hstrong⟩
  refine ⟨A.retypeEndpointStageReference hL hRoof, ?_,
    by simp only [ofOccurrence_localize]⟩
  refine ⟨hvalid.retypeEndpointStageReference hL hRoof, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [CurrentSafeOccurrence.retypeEndpointStageReference_terminal?] using hend
  · intro hs
    exact Set.disjoint_left.mp
      (ColouredSafeEndpointStageReference.vertexSet_disjoint_endpoints (hL := hL))
      hs (Or.inl rfl)
  · intro t ht hmem
    exact Set.disjoint_left.mp
      (ColouredSafeEndpointStageReference.vertexSet_disjoint_endpoints (hL := hL))
      hmem (Or.inr ht)
  · simpa only [CurrentSafeOccurrence.retypeEndpointStageReference_vertexSet] using hRoof
  · intro t het hflag hdeg
    exact hstrong t het hflag
      ((A.hasFiniteSwitchedPathTo_retypeEndpointStageReference_iff hL hRoof
        (hRoof (A.terminal_mem_vertexSet (hend.trans het)))).mp hdeg)

/-- This definition refers to no final owner, final warp, or future stage. -/
def goodAt (L : Gamma.KappaLadder kappa) (a : Stage kappa)
    (s : V) (e : Option V) (strong : Bool) : Set (Trace V) :=
  goodTraces (reference (L.warpAt a) s e) s e strong (Gamma.roof (L.frontier a))

/-- The occurrence's own carrier bound supplies the endpoint-capture
hypothesis. No additional stage or endpoint assumption is needed. -/
theorem goodAt_eq_global_reference (hL : HalfwayGeometry L) :
    goodAt L a s e strong =
      goodTraces (reference L.limitWarp s e) s e strong (Gamma.roof (L.frontier a)) := by
  apply Set.Subset.antisymm
  · intro q hq
    have hends := endpoints_subset_region hq
    apply goodTraces_promote hL
    rw [stageReference_eq_reference_of_endpoints_roof hL hends]
    exact hq
  · intro q hq
    have hends := endpoints_subset_region hq
    have hlocal := goodTraces_localize hL hq
    rw [stageReference_eq_reference_of_endpoints_roof hL hends] at hlocal
    exact hlocal

theorem goodAt_monotone (hL : HalfwayGeometry L) :
    Monotone (fun a : Stage kappa ↦ goodAt L a s e strong) := by
  intro a b hab
  change goodAt L a s e strong ⊆ goodAt L b s e strong
  rw [goodAt_eq_global_reference hL, goodAt_eq_global_reference hL]
  apply goodTraces_mono_region
  rcases hab.lt_or_eq with hab | rfl
  · exact Gamma.roof_cut (hL.frontierChronology hab)
  · exact Set.Subset.rfl

/-- Captured global traces mean an actual global occurrence whose complete
carrier lies in some stage roof, not arbitrary limiting-roof vertices. -/
def captured (L : Gamma.KappaLadder kappa) (s : V) (e : Option V)
    (strong : Bool) : Set (Trace V) :=
  ⋃ a : Stage kappa,
    goodTraces (reference L.limitWarp s e) s e strong (Gamma.roof (L.frontier a))

theorem iUnion_goodAt_eq_captured (hL : HalfwayGeometry L) :
    (⋃ a : Stage kappa, goodAt L a s e strong) = captured L s e strong := by
  simp only [captured, goodAt_eq_global_reference hL]

#print axioms goodTraces_promote
#print axioms goodTraces_localize
#print axioms goodAt_eq_global_reference
#print axioms goodAt_monotone
#print axioms iUnion_goodAt_eq_captured

end Erdos599.Blueprint.ColouredSafeEndpointEligibility
