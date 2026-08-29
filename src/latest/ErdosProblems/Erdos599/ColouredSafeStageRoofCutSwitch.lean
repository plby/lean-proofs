/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeStageRoofCutBoundary
import ErdosProblems.Erdos599.ColouredSafeStageRoofCutSelection
import ErdosProblems.Erdos599.ColouredSafeRoofCutSourceCoverage

/-!
# Protected rooted fixed-stage roof-cut switch

This is the selected interface for the noncausal native occurrence.  First
choose the global occurrence after reserving both the protected set and the
fixed-stage inessential carrier.  Then realize its literal stage-roof cut
and prune away every reentry-rooted component.  The result retains exactly
the touched-reference initials together with the exposed source.

No uniform roof hypothesis on the selected occurrence is used.
-/

noncomputable section

namespace Erdos599

open Set Cardinal Order DirectedPath Alternating Ladder Blueprint
open ColouredSafeReverseReachability ColouredSafeAmbientOccurrence
open Blueprint.ColouredSafeHammock

universe u

variable {V : Type u} {Gamma : DWeb V} {Y0 : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace Blueprint.LinkageBlueprint.ClubStageGeometry

open ColouredSafeStageRoofCutRelation
open ColouredSafeStageRoofCutBoundary

/-- A large global native hammock produces an actual protected, rooted
stage-roof-cut warp.  All endpoints and carrier bounds needed by the later
shortcut/source-coverage and port interfaces are retained. -/
theorem native_global_hasCard_exists_prunedRoofCut
    (C : ClubStageGeometry Gamma Y0 kappa (succ kappa))
    {a : Stage (succ kappa)} (ha : a ∈ C.club) {s : V} {e : Option V}
    {extra : Occurrence C.ladder.limitWarp s → Prop}
    (h : HasCard C.ladder.limitWarp s e extra (succ kappa))
    {X : Set V} (hX : #X ≤ kappa)
    (hsStrict : s ∈ Gamma.strictRoof (C.ladder.frontier a))
    (hsTerminal : ∀ t, e = some t → s ≠ t) :
    ∃ A : Occurrence C.ladder.limitWarp s,
      A ∈ goodRoutes C.ladder.limitWarp s e extra ∧
      A.referenceClosure ∩ X ⊆ endpoints s e ∧
      Disjoint A.referenceClosure (C.inessentialCarrierAt a) ∧
      ∃ P : Set Gamma.DPath,
        Gamma.IsWarp P ∧ Gamma.HasFiniteCharacter P ∧
        Gamma.initialSet P = Gamma.initialSet
          (stageTouchedReference (a := a) A) ∪ {s} ∧
        Gamma.terminalFrontier P ⊆
          C.ladder.frontier a ∪ {x | e = some x} ∧
        Gamma.vertexSet P ⊆ Gamma.roof (C.ladder.frontier a) ∧
        Gamma.vertexSet P ⊆
          Gamma.vertexSet (stageTouchedReference (a := a) A) ∪ A.vertexSet ∧
        Gamma.vertexSet P ⊆ A.referenceClosure ∧
        Gamma.vertexSet P ∩ X ⊆ endpoints s e ∧
        (Gamma.vertexSet P).Countable ∧
        familyEdges P ⊆ A.switchedEdges := by
  obtain ⟨A, hA, hAX, hAbad, _hTouched⟩ :=
    C.native_global_hasCard_exists_occurrence_avoiding_stageInessential
      ha h hX
  have havoid : Disjoint A.vertexSet
      (Gamma.vertexSet (Gamma.inessentialPaths (C.ladder.warpAt a))) := by
    apply Set.disjoint_left.mpr
    intro x hxA hxBad
    exact Set.disjoint_left.mp hAbad (Or.inl hxA) (by
      simpa only [ClubStageGeometry.inessentialCarrierAt] using hxBad)
  have hTouchedLimit : Gamma.vertexSet (stageTouchedReference (a := a) A) ⊆
      Gamma.vertexSet C.ladder.limitWarp := by
    rintro x ⟨p, hp, hxp⟩
    let E := C.legal.stageReferenceEmbedding a
    exact ⟨(E.owner ⟨p, hp.1.1⟩).1, (E.owner ⟨p, hp.1.1⟩).2,
      E.support_subset ⟨p, hp.1.1⟩ hxp⟩
  have hterminalOff : ∀ t, A.terminal? = some t →
      t ∉ Gamma.vertexSet (stageTouchedReference (a := a) A) := by
    intro t ht htTouched
    apply hA.2.2.2.1 t
    · exact hA.2.1.symm.trans ht
    · exact hTouchedLimit htTouched
  have hsOff : s ∉
      Gamma.vertexSet (stageTouchedReference (a := a) A) :=
    fun hs ↦ hA.2.2.1 (hTouchedLimit hs)
  have hsTerminalA : ∀ t, A.terminal? = some t → s ≠ t := by
    intro t ht
    exact hsTerminal t (hA.2.1.symm.trans ht)
  obtain ⟨P, hP, hPfinite, hPinitial, hPterminal, hProof,
      hPcarrier, hPcountable, hPE⟩ :=
    exists_pruned_stageRoofCut C.legal A hA.1 havoid hterminalOff
      hsStrict hsOff hsTerminalA
  have hPclosure : Gamma.vertexSet P ⊆ A.referenceClosure :=
    hPcarrier.trans (Set.union_subset
      (vertexSet_stageTouchedReference_subset_referenceClosure C.legal A)
      Set.subset_union_left)
  have hPterminal' : Gamma.terminalFrontier P ⊆
      C.ladder.frontier a ∪ {x | e = some x} := by
    intro x hx
    rcases hPterminal hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (hA.2.1 ▸ (terminalDefect_eq_one_iff A x).1 hx)
  have hPEglobal : familyEdges P ⊆ A.switchedEdges :=
    hPE.trans (edges_subset_switchedEdges C.legal A
      (fun p hp ↦ hp.1.1) (C.ladder.frontier a))
  exact ⟨A, hA, hAX, hAbad, P, hP, hPfinite, hPinitial,
    hPterminal', hProof, hPcarrier, hPclosure,
    fun _ hx ↦ hAX ⟨hPclosure hx.1, hx.2⟩,
    hPcountable, hPEglobal⟩

#print axioms native_global_hasCard_exists_prunedRoofCut

end Blueprint.LinkageBlueprint.ClubStageGeometry

end Erdos599
