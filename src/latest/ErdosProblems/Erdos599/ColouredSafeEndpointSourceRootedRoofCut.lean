/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointRootedRoofCut

/-!
# Original-source roots in endpoint-pruned roof cuts

Reserve the small carrier of marker-starting essential stage paths. Each
retained touched initial belongs to the rooted output, so a marker initial
would have to be an exposed endpoint. The pruned stage reference excludes
that possibility. No disjointness of the full marker carrier from the
endpoints is assumed.
-/

namespace Erdos599.Blueprint.LinkageBlueprint.ClubStageGeometry

open Set Cardinal Order DirectedPath Ladder
open _root_.Erdos599.Alternating
open ColouredSafeAmbientOccurrence ColouredSafeHammock ColouredSafeEndpointReference

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

theorem endpoint_hasCard_exists_sourceRooted_roofCut
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Stage (succ kappa)} (ha : a ∈ C.club) {s : V} {e : Option V}
    {extra : Occurrence (reference C.ladder.limitWarp s e) s → Prop}
    (h : HasCard (reference C.ladder.limitWarp s e) s e extra (succ kappa))
    {X : Set V} (hX : #X ≤ kappa)
    (hsStrict : s ∈ Gamma.strictRoof (C.ladder.frontier a))
    (hsTerminal : ∀ t, e = some t → s ≠ t) :
    ∃ A : Occurrence (reference C.ladder.limitWarp s e) s,
      A ∈ goodRoutes (reference C.ladder.limitWarp s e) s e extra ∧
      ∃ P : Set Gamma.DPath, Gamma.IsWarp P ∧ Gamma.HasFiniteCharacter P ∧
        Gamma.initialSet P = Gamma.initialSet
          (ColouredSafeEndpointRoofCut.stageTouchedReference C.legal a A) ∪ {s} ∧
        Gamma.terminalFrontier P ⊆ C.ladder.frontier a ∪ {x | e = some x} ∧
        Gamma.vertexSet P ⊆ Gamma.roof (C.ladder.frontier a) ∧
        Gamma.vertexSet P ⊆ Gamma.vertexSet
          (ColouredSafeEndpointRoofCut.stageTouchedReference C.legal a A) ∪ A.vertexSet ∧
        Gamma.vertexSet P ⊆ A.referenceClosure ∧
        Gamma.vertexSet P ∩ X ⊆ endpoints s e ∧
        (Gamma.vertexSet P).Countable ∧ familyEdges P ⊆ A.switchedEdges ∧
        Gamma.initialSet P ⊆ Gamma.source ∪ {s} := by
  let M := Gamma.vertexSet (ladderReference.markerStarting (L := C.ladder) (a := a))
  have hM : #M ≤ kappa :=
    ladderReference.mk_markerStarting_vertices_le C.legal C.capacity_infinite a
  have hXM : #(X ∪ M : Set V) ≤ kappa :=
    (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le C.capacity_infinite hX hM)
  obtain ⟨A, hA, P, hP, hPfinite, hPI, hPT, hPRoof, hPCarrier,
      hPClosure, hPXM, hPcountable, hPE⟩ :=
    C.endpoint_hasCard_exists_protected_rooted_roofCut ha h hXM hsStrict hsTerminal
  have hroots : Gamma.initialSet
      (ColouredSafeEndpointRoofCut.stageTouchedReference C.legal a A) ⊆ Gamma.source := by
    rintro x ⟨q, hq, hqx⟩
    by_contra hxSource
    have hqSource : q.initial ∉ Gamma.source := fun hx ↦ hxSource (hqx ▸ hx)
    have hxM : x ∈ M := ⟨q, ⟨hq.2.1, hqSource⟩, hqx ▸ q.initial_mem_support⟩
    have hxP : x ∈ Gamma.initialSet P := hPI.symm ▸ Or.inl ⟨q, hq, hqx⟩
    have hxEnd : x ∈ endpoints s e :=
      hPXM ⟨initialSet_subset_vertexSet P hxP, Or.inr hxM⟩
    exact Set.disjoint_left.mp ColouredSafeEndpointStageReference.vertexSet_disjoint_endpoints
      ⟨q, hq.1, hqx ▸ q.initial_mem_support⟩ hxEnd
  refine ⟨A, hA, P, hP, hPfinite, hPI, hPT, hPRoof, hPCarrier, hPClosure,
    (fun _ hx ↦ hPXM ⟨hx.1, Or.inl hx.2⟩), hPcountable, hPE, ?_⟩
  rw [hPI]
  exact Set.union_subset_union_left _ hroots

#print axioms endpoint_hasCard_exists_sourceRooted_roofCut

end Erdos599.Blueprint.LinkageBlueprint.ClubStageGeometry
