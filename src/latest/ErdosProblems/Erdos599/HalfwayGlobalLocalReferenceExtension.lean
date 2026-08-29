/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayGlobalLocalReferenceTransport

/-!
# Extending every selected reference member into the limiting reference

The converse half of the global/local reference bridge sends each finite
selected-stage reference member to its unique limiting continuation.  The
map is injective and preserves initials.  This is the owner map needed when
backward links certified against the finite stage reference are reinterpreted
against the global limiting reference.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Ladder Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}
variable {kappa : Cardinal.{u}}

namespace ladderReference

variable {L : Gamma.KappaLadder kappa} {a : Ladder.Stage kappa}

/-- Every member of the finite selected reference has a continuation in the
global limiting reference. -/
theorem exists_limitWarp_extension
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {q : Gamma.DPath} (hq : q ∈ ladderReference L a) :
    ∃ p ∈ L.limitWarp, Gamma.Extends q p := by
  have hKappaLimit : Order.IsSuccLimit kappa.ord :=
    Cardinal.isSuccLimit_ord hL.regular.aleph0_le
  exact hL.limitStages.grows_to_limit
    (Ladder.finalStage kappa) hKappaLimit ⟨a.1, a.2⟩ q hq.1

/-- A fixed global owner for each selected reference member. -/
noncomputable def limitExtension
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (q : ladderReference L a) : Gamma.DPath :=
  Classical.choose (exists_limitWarp_extension hL q.property)

theorem limitExtension_mem
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (q : ladderReference L a) :
    limitExtension hL q ∈ L.limitWarp :=
  (Classical.choose_spec (exists_limitWarp_extension hL q.property)).1

theorem extends_limitExtension
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (q : ladderReference L a) :
    Gamma.Extends q.1 (limitExtension hL q) :=
  (Classical.choose_spec (exists_limitWarp_extension hL q.property)).2

/-- Distinct selected reference members have distinct limiting owners. -/
theorem limitExtension_injective
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L) :
    Function.Injective (limitExtension hL : ladderReference L a → Gamma.DPath) := by
  intro q r hqr
  apply Subtype.ext
  apply DWeb.IsWarp.eq_of_mem_support (ladderReference.isWarp hL)
    q.property r.property q.1.initial_mem_support
  have hinitial : q.1.initial = r.1.initial :=
    (Gamma.extends_initial (extends_limitExtension hL q)).trans
      ((congrArg Path.initial hqr).trans
        (Gamma.extends_initial (extends_limitExtension hL r)).symm)
  exact hinitial ▸ r.1.initial_mem_support

/-- Selected-stage reference initials are genuine limiting-reference
initials; no finite-character claim is made about the limiting family. -/
theorem initialSet_subset_limitWarp
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L) :
    Gamma.initialSet (ladderReference L a) ⊆ Gamma.initialSet L.limitWarp := by
  rintro x ⟨q, hq, hqx⟩
  let qs : ladderReference L a := ⟨q, hq⟩
  refine ⟨limitExtension hL qs, limitExtension_mem hL qs, ?_⟩
  exact (Gamma.extends_initial (extends_limitExtension hL qs)).symm.trans hqx

#print axioms exists_limitWarp_extension
#print axioms limitExtension_injective
#print axioms initialSet_subset_limitWarp

end ladderReference
end Erdos599.Blueprint.LinkageBlueprint
