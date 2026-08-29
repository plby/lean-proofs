/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeHammockOmegaClosure
import ErdosProblems.Erdos599.ColouredSafeReferenceHammockTransport

/-!
# Native hammock closure inside the actual limiting roof

The route filter requires a literal containing stage roof. Thus all selected
carriers lie in the limiting roof, and a small seed in that roof has a small
simultaneously closed superset there. This is a post-limit static existence
theorem; it does not assert causality for a ladder constructed with these
rows, nor the endpoint/incidence hypotheses of an interval transaction.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeHammock

open Set Cardinal DirectedPath Ladder ColouredSafeAmbientOccurrence
open ColouredSafeHammockOmegaClosure

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa rho : Cardinal.{u}}

/-- Actual capture of the complete occurrence carrier by one stage roof. -/
def CapturedByStageRoof (L : Gamma.KappaLadder kappa) (s : V)
    (A : Occurrence L.limitWarp s) : Prop :=
  ∃ a : Stage kappa, A.vertexSet ⊆ Gamma.roof (L.frontier a)

theorem CapturedByStageRoof.vertexSet_subset_limitRoof
    {L : Gamma.KappaLadder kappa} {s : V} {A : Occurrence L.limitWarp s}
    (hA : CapturedByStageRoof L s A) : A.vertexSet ⊆ L.limitRoof := by
  obtain ⟨a, hA⟩ := hA
  intro x hx
  exact Set.mem_iUnion.mpr ⟨a, hA hx⟩

/-- Every actual promoted stage route satisfies the global capture filter. -/
theorem captured_retypeLimitReference
    {L : Gamma.KappaLadder kappa}
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {a : Stage kappa} {s : V}
    (A : ColouredSafeAmbientOccurrence.RoofSupportedAt L a s) :
    CapturedByStageRoof L s (ColouredSafeAmbientOccurrence.retypeLimitReference hL A) := by
  exact ⟨a, by simpa using A.2⟩

/-- A small seed in the limiting roof admits a native closing set in that
same roof, for ordinary and nondegenerate captured routes simultaneously. -/
theorem exists_capturedClosed_superset
    (L : Gamma.KappaLadder kappa) (hrho : aleph0 ≤ rho)
    {X0 : Set V} (hX0 : #X0 ≤ rho) (hX0Roof : X0 ⊆ L.limitRoof) :
    ∃ Z : Set V, X0 ⊆ Z ∧ #Z ≤ rho ∧ Z ⊆ L.limitRoof ∧
      FilteredOmegaClosed L.limitWarp (CapturedByStageRoof L) rho Z := by
  exact exists_filteredOmegaClosed_superset_within L.limitWarp
    (CapturedByStageRoof L) hrho hX0 hX0Roof
    (fun _ _ hA ↦ hA.vertexSet_subset_limitRoof)

#print axioms exists_capturedClosed_superset

end Erdos599.Blueprint.ColouredSafeHammock
