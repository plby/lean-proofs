/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeWeakSourceCoverage
import ErdosProblems.Erdos599.MarkedRayFiniteEdgeStability

/-!
# The complete local native weak blueprint transaction

The six blueprint conditions use native occurrence hammocks throughout.
An actual weak switch, its real companion family, and its ordered edge
subdivision preserve all six conditions. Uniform stage-roof capture and
closing-set containment of the hammock are explicit mathematical inputs.
This does not construct an initial blueprint or a fair infinite schedule.
-/

noncomputable section

namespace Erdos599.ColouredSafeReverseReachability.CurrentSafeOccurrence

open Set DirectedPath Blueprint

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath} {s : V}

theorem referenceClosure_subset_of_closedUnderPaths
    (A : CurrentSafeOccurrence W Y s) {Z : Set V}
    (hZ : ClosedUnderPaths Gamma Y Z) (hA : A.vertexSet ⊆ Z) :
    A.referenceClosure ⊆ Z := by
  rintro x (hxA | hxY)
  · exact hA hxA
  · obtain ⟨p, hxp⟩ := Set.mem_iUnion.mp hxY
    obtain ⟨y, hyp, hyA⟩ := p.2.2
    exact hZ p.1 p.2.1 ⟨y, hyp, hA hyA⟩ hxp

end Erdos599.ColouredSafeReverseReachability.CurrentSafeOccurrence

namespace Erdos599.Blueprint.ColouredSafeShortcutGraph

open Set Cardinal Order DirectedPath Alternating Ladder
open ColouredSafeAmbientOccurrence ColouredSafeReverseReachability ColouredSafeHammock

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- The exact six native blueprint conditions, with the actual warp proof.
The cardinal condition bounds members, as in the source. -/
structure IsLinkageBlueprint (W : Set (imaginaryWeb Y kappa).DPath)
    (T Z persistent : Set V) : Prop where
  isWarp : (imaginaryWeb Y kappa).IsWarp W
  vertices_roofed : (imaginaryWeb Y kappa).vertexSet W ⊆ Gamma.roof T
  covers_source : CoversSource W T
  vertices_closed : (imaginaryWeb Y kappa).vertexSet W ⊆ Z
  card_paths : #W ≤ kappa
  infinitely_many_strong :
    (imaginaryWeb Y kappa).InfinitelyManyMarkedEdges W (IsStrong Y kappa)
  terminals_popular : (imaginaryWeb Y kappa).terminalFrontier W ⊆
    {x | IsPopular Y persistent kappa x} ∪ T

theorem mk_paths_le_vertexSet {D : DWeb V} {W : Set D.DPath} (hW : D.IsWarp W) :
    #W ≤ #(D.vertexSet W) := by
  apply FamilyTools.mk_le_of_pairwiseDisjoint_of_meets
    (F := fun p : D.DPath ↦ p.support)
  · exact hW
  · intro p hp
    exact ⟨p.initial, ⟨p, hp, p.initial_mem_support⟩, p.initial_mem_support⟩

/-- All six conditions survive the actual weak edge transaction. The
selected occurrence and its complete local switch are retained in the result. -/
theorem exists_weakBlueprintTransaction
    (C : LinkageBlueprint.ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Stage (succ kappa)} (ha : a ∈ C.club)
    {Z persistent : Set V}
    (hZ : ClosedUnderPaths Gamma C.ladder.limitWarp Z)
    {W : Set (imaginaryWeb C.ladder.limitWarp kappa).DPath}
    (hW : IsLinkageBlueprint W (C.ladder.frontier a) Z persistent)
    {s t : V} (hne : s ≠ t) (hedge : (s, t) ∈ familyEdges W)
    {extra : Occurrence C.ladder.limitWarp s → Prop}
    (h : HasCard C.ladder.limitWarp s (some t) extra (succ kappa))
    (hroof : ∀ A, extra A → A.vertexSet ⊆ Gamma.roof (C.ladder.frontier a))
    (hclosed : ∀ A, extra A → A.vertexSet ⊆ Z)
    (hnot : ¬HasCard C.ladder.limitWarp s (some t)
      (fun A ↦ extra A ∧ ¬A.HasFiniteSwitchedPathTo t) (succ kappa)) :
    ∃ (A : Occurrence C.ladder.limitWarp s),
      A ∈ goodRoutes C.ladder.limitWarp s (some t) extra ∧
      ∃ hARoof : A.vertexSet ⊆ Gamma.roof (C.ladder.frontier a),
        ∃ T : TouchedWeakSwitch (A.retypeStageReference C.legal hARoof) t,
          ∃ U : Set (imaginaryWeb C.ladder.limitWarp kappa).DPath,
            IsLinkageBlueprint U (C.ladder.frontier a) Z persistent ∧
            (imaginaryWeb C.ladder.limitWarp kappa).initialSet U =
              (imaginaryWeb C.ladder.limitWarp kappa).initialSet W ∪
                Gamma.initialSet (A.retypeStageReference C.legal hARoof).touchedReference ∧
            (imaginaryWeb C.ladder.limitWarp kappa).terminalFrontier U =
              (imaginaryWeb C.ladder.limitWarp kappa).terminalFrontier W ∪
                Gamma.terminalFrontier
                  (A.retypeStageReference C.legal hARoof).touchedReference ∧
            (imaginaryWeb C.ladder.limitWarp kappa).vertexSet U =
              ((imaginaryWeb C.ladder.limitWarp kappa).vertexSet W ∪ T.connector.support) ∪
                Gamma.vertexSet T.companions := by
  let D := imaginaryWeb C.ladder.limitWarp kappa
  have hWcard : #(D.vertexSet W) ≤ kappa :=
    CardinalInduction.HalfwayFrontierHeight.mk_vertexSet_le_of_mk_family_le
      C.capacity_infinite W hW.card_paths
  obtain ⟨A, hA, hARoof, T, hcomp, hconn, hTRoof, hEss⟩ :=
    C.native_global_weak_hasCard_exists_essentialTouchedSwitch_avoiding
      ha hne h hroof hnot hWcard
  have hstageV : Gamma.vertexSet (C.ladder.warpAt a) ⊆
      Gamma.vertexSet C.ladder.limitWarp := by
    rintro x ⟨p, hp, hxp⟩
    let E := C.legal.stageReferenceEmbedding a
    exact ⟨(E.owner ⟨p, hp⟩).1, (E.owner ⟨p, hp⟩).2, E.support_subset ⟨p, hp⟩ hxp⟩
  have hs : s ∉ Gamma.vertexSet (C.ladder.warpAt a) :=
    fun hv ↦ hA.2.2.1 (hstageV hv)
  have ht : t ∉ Gamma.vertexSet (C.ladder.warpAt a) :=
    fun hv ↦ hA.2.2.2.1 t rfl (hstageV hv)
  obtain ⟨U, hU, hUI, hUT, hUV, htrace⟩ :=
    exists_weakSubdivision_with_companions_and_rayTrace T hs ht
      hW.isWarp hedge hconn hcomp
  have hUVsub : D.vertexSet U ⊆ D.vertexSet W ∪ Gamma.vertexSet T.paths := by
    rw [hUV]
    rintro x ((hxW | hxConnector) | hxCompanion)
    · exact Or.inl hxW
    · exact Or.inr ⟨.inl T.connector, T.connector_mem, hxConnector⟩
    · obtain ⟨p, hp, hxp⟩ := hxCompanion
      exact Or.inr ⟨p, hp.1, hxp⟩
  have hTClosed : Gamma.vertexSet T.paths ⊆ Z :=
    T.carrier_subset.trans
      ((A.retypeStageReference_referenceClosure_subset C.legal hARoof).trans
        (A.referenceClosure_subset_of_closedUnderPaths hZ (hclosed A hA.2.2.2.2)))
  have hUcard : #(D.vertexSet U) ≤ kappa :=
    (Cardinal.mk_le_mk_of_subset hUVsub).trans
      ((Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le
        C.capacity_infinite hWcard (T.carrier_countable.le_aleph0.trans C.capacity_infinite)))
  have hcover : CoversSource U (C.ladder.frontier a) := by
    apply coversSource_of_stageWeakSwitch C.legal hARoof T hs hTRoof hW.covers_source
    · rw [hUI]
      exact Set.subset_union_left
    · rw [hUI, T.companions_initialSet hs]
      exact Set.subset_union_right
    · exact hUVsub
  have hnewTerminals : Gamma.terminalFrontier
      (A.retypeStageReference C.legal hARoof).touchedReference ⊆ C.ladder.frontier a := by
    rintro x ⟨p, hp, hpx⟩
    rw [← LinkageBlueprint.ladderReference.terminalFrontier_eq C.legal]
    exact ⟨p, hEss hp, hpx⟩
  refine ⟨A, hA, hARoof, T, U, ?_, hUI, hUT, hUV⟩
  exact {
    isWarp := hU
    vertices_roofed := hUVsub.trans (Set.union_subset hW.vertices_roofed hTRoof)
    covers_source := hcover
    vertices_closed := hUVsub.trans (Set.union_subset hW.vertices_closed hTClosed)
    card_paths := (mk_paths_le_vertexSet hU).trans hUcard
    infinitely_many_strong := DWeb.infinitelyManyMarkedEdges_of_rayTrace
      hW.infinitely_many_strong (Set.finite_singleton (s, t)) htrace
    terminals_popular := by
      rw [hUT]
      exact Set.union_subset hW.terminals_popular
        (hnewTerminals.trans Set.subset_union_right) }

#print axioms mk_paths_le_vertexSet
#print axioms exists_weakBlueprintTransaction

end Erdos599.Blueprint.ColouredSafeShortcutGraph
