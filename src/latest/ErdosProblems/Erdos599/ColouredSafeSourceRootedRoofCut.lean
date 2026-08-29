/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeStageRoofCutSwitch

/-!
# Protected roof-cut selection avoiding marker-starting reference members

At one fixed stage, the marker-starting essential reference has a small
carrier. Reserve it before selecting the global occurrence. Since exposed
ends lie off the limiting reference, the whole selected reference closure
avoids that carrier. Every touched stage-reference initial is then an
original source, and the pruned roof cut is rooted in those sources plus
the one exposed port. No source-rootedness premise is added to the graph.
-/

namespace Erdos599.Blueprint.LinkageBlueprint.ClubStageGeometry

open Set Cardinal Order DirectedPath Alternating Ladder
open ColouredSafeAmbientOccurrence ColouredSafeHammock ColouredSafeStageRoofCutRelation

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

/-- The rooted roof cut can be chosen with no marker-starting reference
component, while preserving the entire original selection interface. -/
theorem native_global_hasCard_exists_sourceRootedRoofCut
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
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
        Gamma.initialSet P = Gamma.initialSet (stageTouchedReference (a := a) A) ∪ {s} ∧
        Gamma.terminalFrontier P ⊆ C.ladder.frontier a ∪ {x | e = some x} ∧
        Gamma.vertexSet P ⊆ Gamma.roof (C.ladder.frontier a) ∧
        Gamma.vertexSet P ⊆
          Gamma.vertexSet (stageTouchedReference (a := a) A) ∪ A.vertexSet ∧
        Gamma.vertexSet P ⊆ A.referenceClosure ∧
        Gamma.vertexSet P ∩ X ⊆ endpoints s e ∧
        (Gamma.vertexSet P).Countable ∧ familyEdges P ⊆ A.switchedEdges ∧
        Gamma.initialSet (stageTouchedReference (a := a) A) ⊆ Gamma.source ∧
        Gamma.initialSet P ⊆ Gamma.source ∪ {s} := by
  let M := Gamma.vertexSet
    (ladderReference.markerStarting (L := C.ladder) (a := a))
  have hM : #M ≤ kappa :=
    ladderReference.mk_markerStarting_vertices_le C.legal C.capacity_infinite a
  have hXM : #(X ∪ M : Set V) ≤ kappa :=
    (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le C.capacity_infinite hX hM)
  obtain ⟨A, hA, hAXM, hAbad, P, hP, hPfin, hPI, hPT, hProof,
      hPcarrier, hPclosure, hPXM, hPcount, hPE⟩ :=
    C.native_global_hasCard_exists_prunedRoofCut ha h hXM hsStrict hsTerminal
  have hMlimit : M ⊆ Gamma.vertexSet C.ladder.limitWarp := by
    rintro x ⟨p, hp, hxp⟩
    let E := C.legal.stageReferenceEmbedding a
    exact ⟨(E.owner ⟨p, hp.1.1⟩).1, (E.owner ⟨p, hp.1.1⟩).2,
      E.support_subset ⟨p, hp.1.1⟩ hxp⟩
  have hAM : Disjoint A.referenceClosure M := by
    apply Set.disjoint_left.mpr
    intro x hxA hxM
    rcases hAXM ⟨hxA, Or.inr hxM⟩ with hxs | hxt
    · exact hA.2.2.1 (Set.mem_singleton_iff.mp hxs ▸ hMlimit hxM)
    · exact hA.2.2.2.1 x hxt (hMlimit hxM)
  have hIS : Gamma.initialSet (stageTouchedReference (a := a) A) ⊆ Gamma.source := by
    rintro x ⟨p, hp, hpx⟩
    have hpSource : p.initial ∈ Gamma.source := by
      by_contra hnot
      obtain ⟨y, hyp, hyA⟩ := hp.2
      exact Set.disjoint_left.mp hAM (Or.inl hyA) ⟨p, ⟨hp.1, hnot⟩, hyp⟩
    exact hpx ▸ hpSource
  refine ⟨A, hA, ?_, hAbad, P, hP, hPfin, hPI, hPT, hProof,
    hPcarrier, hPclosure, ?_, hPcount, hPE, hIS, ?_⟩
  · exact fun _ hx ↦ hAXM ⟨hx.1, Or.inl hx.2⟩
  · exact fun _ hx ↦ hPXM ⟨hx.1, Or.inl hx.2⟩
  · rw [hPI]
    exact Set.union_subset_union_left _ hIS

#print axioms native_global_hasCard_exists_sourceRootedRoofCut

end Erdos599.Blueprint.LinkageBlueprint.ClubStageGeometry
