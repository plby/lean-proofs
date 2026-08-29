/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingErasedDecode
import ErdosProblems.Erdos599.GroundingRootedReachabilityWarp

/-!
# The exact antichain obstruction in the pre-stopped grounding relation

The empty-frontier switch deliberately leaves every boundary continuation
in place.  Consequently a residual edge between two boundary vertices
survives unless a selected backward edge or a forward-incidence conflict
deletes that particular edge.  Assertion 8.21 only orders such contacts; it
does not supply either deletion.

The results below isolate the precise local obstruction to the antichain
callback of the pre-stopped Assertion 8.22 compiler.  They are stated for
the actual selected relation, rather than for an abstract residual base.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingPreStoppedAntichainAudit

open GroundingErasedDecode GroundingRootedReachabilityWarp

universe u

variable {V I : Type u} {Gamma : DWeb V}

/-- A residual edge survives the empty-frontier switch whenever it is
neither a selected backward edge nor incident-conflicting with a selected
forward edge.  There is no boundary-outgoing deletion at the empty
frontier. -/
theorem residualEdge_mem_preStopped_of_not_selected
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) {b c : V}
    (hresidual : (b, c) ∈ residualLadderEdges U S)
    (hbackward : (b, c) ∉
      erasedSelectedDirectionEdgesAt U S K ∅ .backward)
    (hconflict : (b, c) ∉ forwardConflictCutEdgesAt U S K ∅) :
    (b, c) ∈ erasedSelectedSwitchedEdgesAt U S K ∅ := by
  rw [erasedSelectedSwitchedEdgesAt_empty_eq]
  refine Or.inl ⟨hresidual, ?_⟩
  rintro (hback | hconf)
  · exact hbackward hback
  · exact hconflict hconf

/-- One surviving residual edge between distinct points of the literal
grounding boundary refutes the exact reachability-antichain premise used by
the pre-stopped compiler. -/
theorem not_reachabilityAntichain_of_surviving_residualEdge
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) {b c : V}
    (hb : b ∈ GroundingCut.BB L S.cut)
    (hc : c ∈ GroundingCut.BB L S.cut) (hne : b ≠ c)
    (hresidual : (b, c) ∈ residualLadderEdges U S)
    (hbackward : (b, c) ∉
      erasedSelectedDirectionEdgesAt U S K ∅ .backward)
    (hconflict : (b, c) ∉ forwardConflictCutEdgesAt U S K ∅) :
    ¬ IsReachabilityAntichain
      (erasedSelectedSwitchedEdgesAt U S K ∅)
      (GroundingCut.BB L S.cut) := by
  intro hanti
  apply hne
  exact hanti hb hc (Relation.ReflTransGen.single
    (residualEdge_mem_preStopped_of_not_selected U S K
      hresidual hbackward hconflict))

end GroundingPreStoppedAntichainAudit
end Erdos599

#print axioms
  Erdos599.GroundingPreStoppedAntichainAudit.residualEdge_mem_preStopped_of_not_selected
#print axioms
  Erdos599.GroundingPreStoppedAntichainAudit.not_reachabilityAntichain_of_surviving_residualEdge
