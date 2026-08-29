/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAssembly
import ErdosProblems.Erdos599.LambdaCutCompression

/-!
# Decoding the control-aware selected auxiliary paths

Every Section 8 request is represented by an old vertex or an edge gadget.
Both kinds have a canonical original exit.  Consequently every path in the
control-aware selected auxiliary warp has the endpoint witness required by
the cut-relaxed Lambda decoder.

This is a pathwise result.  It deliberately makes no global disjointness or
switching claim about the decoded traces; those are the remaining content of
Assertions 8.19--8.22.
-/

noncomputable section

namespace Erdos599
namespace GroundingSelectedDecoder

open DirectedPath
open PopularGroundingBridge

universe u

variable {V I : Type u} {Gamma : DWeb V}

/-- The auxiliary representative of every request has a genuine original
exit.  For an old request it is the old vertex; for an edge request it is
the tail of the represented edge. -/
theorem requestAuxVertex_has_gadgetExit
    {L : PopularAuxiliary.Input Gamma I}
    {C : Set (PopularAuxiliary.Input.LambdaVertex V I)}
    (r : Request L C) :
    ∃ z, L.gadgetExit (requestAuxVertex r) = some z := by
  cases r with
  | inl x => exact ⟨x.1, rfl⟩
  | inr e => exact ⟨e.1.1, rfl⟩

/-- The recursively selected path at a request has a genuine original exit
at its terminal gadget. -/
theorem selectedPath_has_gadgetExit
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    ∃ z, L.gadgetExit (GroundingAssembly.selectedPath U S K r).finish =
      some z := by
  obtain ⟨z, hz⟩ := requestAuxVertex_has_gadgetExit r
  refine ⟨z, ?_⟩
  rw [GroundingAssembly.selectedPath_finish U S K r]
  exact hz

/-- The certified cut-ending micro-trace of a selected request path. -/
noncomputable def selectedCutMicroTrace
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    L.CutMicroTrace (GroundingAssembly.selectedPath U S K r) := by
  have hp : GroundingAssembly.selectedPath U S K r ∈
      (GroundingAssembly.selectedWarp U S K).paths := ⟨r, rfl⟩
  exact L.decodeFinitePathToExit
    (GroundingAssembly.selectedPath U S K r)
    ((GroundingAssembly.selectedWarp U S K).starts_in_source hp)
    (selectedPath_has_gadgetExit S K r)

@[simp]
theorem selectedCutMicroTrace_steps
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    (selectedCutMicroTrace S K r).steps =
      L.decodeWalkSteps (GroundingAssembly.selectedPath U S K r).walk := by
  have hp : GroundingAssembly.selectedPath U S K r ∈
      (GroundingAssembly.selectedWarp U S K).paths := ⟨r, rfl⟩
  exact L.decodeFinitePathToExit_steps
    (GroundingAssembly.selectedPath U S K r)
    ((GroundingAssembly.selectedWarp U S K).starts_in_source hp)
    (selectedPath_has_gadgetExit S K r)

end GroundingSelectedDecoder
end Erdos599
