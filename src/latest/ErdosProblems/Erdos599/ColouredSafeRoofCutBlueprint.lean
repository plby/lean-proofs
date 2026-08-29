/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeRoofCutSourceCoverage
import ErdosProblems.Erdos599.ColouredSafeWeakBlueprintTransaction

/-!
# The six blueprint conditions from an actual roof-cut insertion

The criterion uses the actual replacement carrier's roof containment and
touched-reference provenance, not uniform roofedness of the global word.
It applies to the two-port, one-sided, and terminal insertion constructions.
The constructors must prove the displayed boundary and ray-trace premises.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeShortcutGraph

open Set Cardinal Order DirectedPath Alternating Ladder
open ColouredSafeAmbientOccurrence ColouredSafeReverseReachability ColouredSafeStageRoofCutRelation

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- Source exposure implies that adjoining the distinguished source and
then removing it leaves exactly the touched reference initials. -/
theorem roofCut_initials_sdiff_source
    {rho : Cardinal.{u}} {L : Gamma.KappaLadder rho} {a : Stage rho}
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {s : V} (A : Occurrence L.limitWarp s)
    (hs : s ∉ Gamma.vertexSet L.limitWarp)
    {K : Set Gamma.DPath}
    (hKI : Gamma.initialSet K =
      Gamma.initialSet (stageTouchedReference (a := a) A) ∪ {s}) :
    Gamma.initialSet K \ {s} =
      Gamma.initialSet (stageTouchedReference (a := a) A) := by
  have hsRef : s ∉ Gamma.initialSet (stageTouchedReference (a := a) A) := by
    rintro ⟨p, hp, hps⟩
    let E := hL.stageReferenceEmbedding a
    exact hs ⟨(E.owner ⟨p, hp.1.1⟩).1, (E.owner ⟨p, hp.1.1⟩).2,
      E.support_subset ⟨p, hp.1.1⟩ (hps ▸ p.initial_mem_support)⟩
  rw [hKI]
  ext x
  simp only [Set.mem_sdiff, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx | hx, hne⟩
    · exact hx
    · exact False.elim (hne hx)
  · intro hx
    exact ⟨Or.inl hx, fun hxs ↦ hsRef (hxs ▸ hx)⟩

/-- Actual carrier, boundary and ray trace facts imply all six native
blueprint conditions. Uniform capture of the occurrence is not a premise. -/
theorem isLinkageBlueprint_of_roofCutInsertion
    (C : LinkageBlueprint.ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Stage (succ kappa)} {Z persistent : Set V}
    (hZ : ClosedUnderPaths Gamma C.ladder.limitWarp Z)
    {W : Set (imaginaryWeb C.ladder.limitWarp kappa).DPath}
    (hW : IsLinkageBlueprint W (C.ladder.frontier a) Z persistent)
    {s : V} (A : Occurrence C.ladder.limitWarp s)
    (hAclosed : A.vertexSet ⊆ Z)
    {K : Set Gamma.DPath}
    (hKroof : Gamma.vertexSet K ⊆ Gamma.roof (C.ladder.frontier a))
    (hKcarrier : Gamma.vertexSet K ⊆
      Gamma.vertexSet (stageTouchedReference (a := a) A) ∪ A.vertexSet)
    (hKcountable : (Gamma.vertexSet K).Countable)
    {U : Set (imaginaryWeb C.ladder.limitWarp kappa).DPath}
    (hU : (imaginaryWeb C.ladder.limitWarp kappa).IsWarp U)
    (hIold : (imaginaryWeb C.ladder.limitWarp kappa).initialSet W ⊆
      (imaginaryWeb C.ladder.limitWarp kappa).initialSet U)
    (hIreference : Gamma.initialSet (stageTouchedReference (a := a) A) ⊆
      (imaginaryWeb C.ladder.limitWarp kappa).initialSet U)
    (hterminals : (imaginaryWeb C.ladder.limitWarp kappa).terminalFrontier U ⊆
      (imaginaryWeb C.ladder.limitWarp kappa).terminalFrontier W ∪ C.ladder.frontier a)
    (hcarrier : (imaginaryWeb C.ladder.limitWarp kappa).vertexSet U ⊆
      (imaginaryWeb C.ladder.limitWarp kappa).vertexSet W ∪ Gamma.vertexSet K)
    (htrace : ∀ r : Ray (imaginaryWeb C.ladder.limitWarp kappa).graph, Sum.inr r ∈ U →
      ∃ r0 : Ray (imaginaryWeb C.ladder.limitWarp kappa).graph, Sum.inr r0 ∈ W ∧
        ∃ lost : Set (V × V), lost.Finite ∧ r0.edgeSet \ lost ⊆ r.edgeSet) :
    IsLinkageBlueprint U (C.ladder.frontier a) Z persistent := by
  let D := imaginaryWeb C.ladder.limitWarp kappa
  have hKclosed : Gamma.vertexSet K ⊆ Z :=
    (hKcarrier.trans (Set.union_subset
      (vertexSet_stageTouchedReference_subset_referenceClosure C.legal A)
      Set.subset_union_left)).trans
        (A.referenceClosure_subset_of_closedUnderPaths hZ hAclosed)
  have hWcard : #(D.vertexSet W) ≤ kappa :=
    CardinalInduction.HalfwayFrontierHeight.mk_vertexSet_le_of_mk_family_le
      C.capacity_infinite W hW.card_paths
  have hUcard : #(D.vertexSet U) ≤ kappa :=
    (Cardinal.mk_le_mk_of_subset hcarrier).trans
      ((Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le
        C.capacity_infinite hWcard (hKcountable.le_aleph0.trans C.capacity_infinite)))
  exact {
    isWarp := hU
    vertices_roofed := hcarrier.trans (Set.union_subset hW.vertices_roofed hKroof)
    covers_source := coversSource_of_roofCut C.legal A hKroof hKcarrier
      hW.covers_source hIold hIreference hcarrier
    vertices_closed := hcarrier.trans (Set.union_subset hW.vertices_closed hKclosed)
    card_paths := (mk_paths_le_vertexSet hU).trans hUcard
    infinitely_many_strong := DWeb.infinitelyManyMarkedEdges_of_finite_rayTrace
      hW.infinitely_many_strong htrace
    terminals_popular := hterminals.trans
      (Set.union_subset hW.terminals_popular Set.subset_union_right) }

#print axioms roofCut_initials_sdiff_source
#print axioms isLinkageBlueprint_of_roofCutInsertion

end Erdos599.Blueprint.ColouredSafeShortcutGraph
