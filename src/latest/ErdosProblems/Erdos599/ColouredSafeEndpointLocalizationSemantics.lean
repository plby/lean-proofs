/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointReferenceLocalization
import ErdosProblems.Erdos599.ColouredSafeTouchedReferenceSwitch

/-!
# Switching semantics for the owner-pruned stage reference

Localization preserves finite switched reachability to a roofed terminal.
The backward-roof argument applies to the actual pruned reference relation;
it does not identify it with the full reference. Intrinsic validity and
the touched-reference carrier bound also survive the literal retyping.
-/

noncomputable section

namespace Erdos599.ColouredSafeReverseReachability.CurrentSafeOccurrence

open Set Cardinal DirectedPath Alternating Ladder Blueprint
open DWeb.KappaLadder.Deferred ColouredSafeAmbientOccurrence
open ColouredSafeEndpointReference ColouredSafeEndpointStageReference

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {a : Stage kappa}
variable {W : Set Gamma.DPath} {s t : V} {e : Option V}

theorem retypeEndpointStageReference_switchedEdges_subset
    (hL : HalfwayGeometry L) (A : CurrentSafeOccurrence W (reference L.limitWarp s e) s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (A.retypeEndpointStageReference hL hRoof).switchedEdges ⊆ A.switchedEdges := by
  intro edge he
  rcases he with hreference | hforward
  · exact Or.inl ⟨(embedding hL a s e).familyEdges_subset hreference.1,
      by simpa only [retypeEndpointStageReference_backwardEdges] using hreference.2⟩
  · exact Or.inr (by simpa only [retypeEndpointStageReference_forwardEdges] using hforward)

theorem mem_endpointStage_switchedEdges_of_head_roof
    (hL : HalfwayGeometry L) (A : CurrentSafeOccurrence W (reference L.limitWarp s e) s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a))
    {edge : V × V} (he : edge ∈ A.switchedEdges)
    (hyRoof : edge.2 ∈ Gamma.roof (L.frontier a)) :
    edge ∈ (A.retypeEndpointStageReference hL hRoof).switchedEdges := by
  rcases he with hreference | hforward
  · exact Or.inl ⟨incoming_edge_reflect hL hreference.1 hyRoof,
      by simpa only [retypeEndpointStageReference_backwardEdges] using hreference.2⟩
  · exact Or.inr (by simpa only [retypeEndpointStageReference_forwardEdges] using hforward)

/-- No global switched path ending in the roof can enter that roof late. -/
theorem finitePath_support_subset_roof_of_endpointReference
    (hL : HalfwayGeometry L) (A : CurrentSafeOccurrence W (reference L.limitWarp s e) s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a))
    {p : FinitePath Gamma.graph} (hpEdges : p.edgeSet ⊆ A.switchedEdges)
    (hfinishRoof : p.finish ∈ Gamma.roof (L.frontier a)) :
    p.support ⊆ Gamma.roof (L.frontier a) := by
  have hback : ∀ {x y}, (x, y) ∈ p.edgeSet → y ∈ Gamma.roof (L.frontier a) →
      x ∈ Gamma.roof (L.frontier a) := by
    intro x y hxy hyRoof
    rcases hpEdges hxy with hreference | hforward
    · exact edge_tail_roof_of_head_roof hL hreference.1 hyRoof
    · apply hRoof
      cases A with
      | finite t Q => exact (Q.forwardEdges_endpoints_mem_vertexSet hforward).1
      | infinite Q => exact (Q.forwardEdges_endpoints_mem_vertexSet hforward).1
  intro x hxp
  let q := p.suffixFrom x hxp
  have hq := DWeb.KappaLadder.Walk.start_mem_of_meets_of_backwardClosed
    (w := q.walk) (R := Gamma.roof (L.frontier a))
    (fun {_y _z} hyz hzRoof ↦ hback (p.suffixFrom_edgeSet_subset x hxp hyz) hzRoof)
    ⟨p.finish, q.finish_mem_support, by simpa [q] using hfinishRoof⟩
  simpa [q] using hq

theorem hasFiniteSwitchedPathTo_retypeEndpointStageReference_iff
    (hL : HalfwayGeometry L) (A : CurrentSafeOccurrence W (reference L.limitWarp s e) s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a))
    (htRoof : t ∈ Gamma.roof (L.frontier a)) :
    (A.retypeEndpointStageReference hL hRoof).HasFiniteSwitchedPathTo t ↔
      A.HasFiniteSwitchedPathTo t := by
  constructor
  · rintro ⟨p, hps, hpt, hpEdges⟩
    exact ⟨p, hps, hpt, hpEdges.trans (A.retypeEndpointStageReference_switchedEdges_subset
      hL hRoof)⟩
  · rintro ⟨p, hps, hpt, hpEdges⟩
    have hpRoof := A.finitePath_support_subset_roof_of_endpointReference hL hRoof
      hpEdges (hpt.symm ▸ htRoof)
    exact ⟨p, hps, hpt, fun edge he ↦
      A.mem_endpointStage_switchedEdges_of_head_roof hL hRoof (hpEdges he)
        (hpRoof (p.edgeSet_subset_support_prod he).2)⟩

/-- Every localized touched prefix is contained in a touched retained
limiting owner, so no excluded endpoint owner is silently reintroduced. -/
theorem retypeEndpointStageReference_referenceClosure_subset
    (hL : HalfwayGeometry L) (A : CurrentSafeOccurrence W (reference L.limitWarp s e) s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (A.retypeEndpointStageReference hL hRoof).referenceClosure ⊆ A.referenceClosure := by
  rintro x (hxA | hxOwner)
  · exact Or.inl (by simpa only [retypeEndpointStageReference_vertexSet] using hxA)
  · obtain ⟨p, hxp⟩ := Set.mem_iUnion.mp hxOwner
    let E := embedding hL a s e
    let q := E.owner ⟨p.1, p.2.1⟩
    have hxq := E.support_subset ⟨p.1, p.2.1⟩ hxp
    obtain ⟨y, hyp, hyA⟩ := p.2.2
    exact Or.inr (support_subset_meetingVertices Gamma (reference L.limitWarp s e)
      A.vertexSet q.2 ⟨y, E.support_subset ⟨p.1, p.2.1⟩ hyp,
        by simpa only [retypeEndpointStageReference_vertexSet] using hyA⟩ hxq)

#print axioms hasFiniteSwitchedPathTo_retypeEndpointStageReference_iff
#print axioms retypeEndpointStageReference_referenceClosure_subset

end Erdos599.ColouredSafeReverseReachability.CurrentSafeOccurrence

namespace Erdos599.ColouredSafeAmbientOccurrence

open Set Cardinal DirectedPath Ladder Blueprint
open DWeb.KappaLadder.Deferred ColouredSafeReverseReachability
open ColouredSafeEndpointReference

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {a : Stage kappa} {s : V} {e : Option V}

theorem Valid.retypeEndpointStageReference (hL : HalfwayGeometry L)
    {A : Occurrence (reference L.limitWarp s e) s} (hA : Valid A)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    Valid (A.retypeEndpointStageReference hL hRoof) := by
  obtain ⟨W, hW, hfinite, hEdges⟩ := hA
  exact ⟨W, hW, hfinite, by simpa only
    [CurrentSafeOccurrence.retypeEndpointStageReference_forwardEdges] using hEdges⟩

#print axioms Valid.retypeEndpointStageReference

end Erdos599.ColouredSafeAmbientOccurrence
