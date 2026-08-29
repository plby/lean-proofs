/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeReferenceLocalization
import ErdosProblems.Erdos599.ColouredSafeReferenceTransportSemantics

/-!
# Exact equivalence of roof-supported native route types

Promotion and localization are inverse literal reference retypings. The
equivalence retains the entire chronological route, not just its endpoint
or its carrier, and preserves finite switched reachability.
-/

namespace Erdos599.ColouredSafeReverseReachability.CurrentSafeOccurrence

open Set Cardinal DirectedPath Alternating Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {a : Stage kappa}
variable {current : Set Gamma.DPath} {s t : V}

@[simp] theorem retypeLimitReference_retypeStageReference
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : CurrentSafeOccurrence current L.limitWarp s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (A.retypeStageReference hL hRoof).retypeLimitReference hL
      (by simpa using hRoof) = A := by
  cases A <;> rfl

@[simp] theorem retypeStageReference_retypeLimitReference
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : CurrentSafeOccurrence current (L.warpAt a) s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (A.retypeLimitReference hL hRoof).retypeStageReference hL
      (by simpa using hRoof) = A := by
  cases A <;> rfl

/-- The actual stage/global equivalence of safe occurrences in one roof.
It works with every fixed forward-family parameter. -/
def roofSupportedReferenceEquiv
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L) :
    {A : CurrentSafeOccurrence current (L.warpAt a) s //
      A.vertexSet ⊆ Gamma.roof (L.frontier a)} ≃
    {A : CurrentSafeOccurrence current L.limitWarp s //
      A.vertexSet ⊆ Gamma.roof (L.frontier a)} where
  toFun A := ⟨A.1.retypeLimitReference hL A.2, by simpa using A.2⟩
  invFun A := ⟨A.1.retypeStageReference hL A.2, by simpa using A.2⟩
  left_inv A := by
    apply Subtype.ext
    exact retypeStageReference_retypeLimitReference hL A.1 A.2
  right_inv A := by
    apply Subtype.ext
    exact retypeLimitReference_retypeStageReference hL A.1 A.2

theorem hasFiniteSwitchedPathTo_retypeStageReference_iff
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : CurrentSafeOccurrence current L.limitWarp s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a))
    (htRoof : t ∈ Gamma.roof (L.frontier a)) :
    (A.retypeStageReference hL hRoof).HasFiniteSwitchedPathTo t ↔
      A.HasFiniteSwitchedPathTo t := by
  have h := hasFiniteSwitchedPathTo_retypeLimitReference_iff hL
    (A.retypeStageReference hL hRoof) (by simpa using hRoof) htRoof
  simpa only [retypeLimitReference_retypeStageReference] using h.symm

#print axioms roofSupportedReferenceEquiv
#print axioms hasFiniteSwitchedPathTo_retypeStageReference_iff

end Erdos599.ColouredSafeReverseReachability.CurrentSafeOccurrence
