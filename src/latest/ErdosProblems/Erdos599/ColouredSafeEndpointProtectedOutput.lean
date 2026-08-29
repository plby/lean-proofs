/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointCompletedProjection
import ErdosProblems.Erdos599.CarrierLocalizedReferenceRemainder
import ErdosProblems.Erdos599.HalfwayLocalizedProtectedGeometry
import ErdosProblems.Erdos599.EssentialPartUnhinderedTransfer

/-!
# The actual endpoint construction gives protected half-way geometry

The two original-graph families are the completed source paths and finite
disjoint prefixes of the selected-stage reference. The same club frontier
supplies the separator, trimmedness, two unhindered quotients and height.
No terminal-clean condition is imposed on the completed target track.
-/

namespace Erdos599.Blueprint.LinkageBlueprint

open Set Cardinal Order DirectedPath Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

/-- Deferred legality and the actual avoiding-club membership give the full
frontier quotient, not just its essential induced subweb. -/
theorem ClubStageGeometry.frontier_quotient_isUnhindered
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Stage (succ kappa)} (ha : a ∈ C.club) :
    (Gamma.quotient (C.ladder.frontier a)).IsUnhindered := by
  let T := Gamma.terminalFrontier (C.ladder.warpAt a)
  have hroofT : Gamma.source ⊆ Gamma.roof T :=
    C.legal.roofsSourceAtStages (Ladder.Stage.toExtended a)
  have hfrontier : C.ladder.frontier a = Gamma.essential T :=
    C.ladder.frontier_eq_essential_terminalFrontier C.legal.roofsSourceAtStages a
  have hquotient : Gamma.quotient (C.ladder.frontier a) = Gamma.quotient T := by
    rw [hfrontier]
    exact Gamma.quotient_essential_eq_of_subset_roof T hroofT
  apply DWeb.isUnhindered_of_essentialPart_of_source_eq
    (Gamma.quotient (C.ladder.frontier a))
  · rw [hquotient]
    have hleft : (Gamma.quotient T).essentialPart.source = Gamma.essential T :=
      Gamma.quotientEssentialPart_source_eq_essential_of_roofsSource hroofT
    have hright : (Gamma.quotient T).source = Gamma.essential T := by
      rw [DWeb.quotient_source, Set.union_comm]
      exact RelationalRoof.essential_union_eq_of_subset_roof Gamma.graph.Adj Gamma.target hroofT
    exact hleft.trans hright.symm
  · rw [hquotient]
    exact C.stageWeb_isUnhindered ha

#print axioms ClubStageGeometry.frontier_quotient_isUnhindered

end Erdos599.Blueprint.LinkageBlueprint

namespace Erdos599.Blueprint.ColouredSafeEndpointBlueprint.StableState

open Set Cardinal Order DirectedPath Ladder LinkageBlueprint
open _root_.Erdos599.CardinalInduction

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)} {Z : Set V}

/-- Every field of the protected geometry is constructed from the fully
completed state and actual ladder data. The retained reference is finite
and terminal-clean; the target family need not avoid the stopover internally. -/
theorem exists_localizedProtectedGeometry (S : StableState C Z)
    (hcomplete : S.carrier ⊆ S.completed) {A0 : Set V}
    (hA0source : A0 ⊆ Gamma.source) (hA0carrier : A0 ⊆ S.carrier) :
    Nonempty (LinkageBlueprint.CardinalInduction.LocalizedProtectedHalfwayGeometry
      Gamma A0 kappa) := by
  obtain ⟨P, hP, _hPE, hPV, hPcard, hcover⟩ := S.exists_linkageProjection hcomplete
  let R := carrierReferenceRemainder C.ladder S.index (Gamma.vertexSet P)
  have hsource : Gamma.initialSet P ⊆ Gamma.source := by
    rw [hP.initialSet_eq]
    exact Set.inter_subset_left
  have hdesignated : A0 ⊆ Gamma.initialSet P := by
    intro x hx
    exact hP.initialSet_eq ▸ ⟨hA0source hx, hA0carrier hx⟩
  have hlinks (A : Set V) (hA : A ⊆ Gamma.source) (hAi : A ⊆ Gamma.initialSet P) :
      LinksToTarget Gamma P A := by
    apply SingularContinuation.linksToTarget_of_initial_terminal Gamma C.normalized
      hP.finiteCharacter hA
    intro x hx
    obtain ⟨p, hp, hpx⟩ := hAi hx
    obtain ⟨q, rfl⟩ := hP.finiteCharacter hp
    exact ⟨.inl q, hp, hpx, q.finish, hP.terminalFrontier_subset ⟨.inl q, hp, rfl⟩, rfl⟩
  have hroof : Gamma.vertexSet P ⊆ Gamma.roof (C.ladder.frontier S.index) :=
    hPV.trans S.blueprint.vertices_roofed
  have hseparator : IsSeparatorFrom Gamma Gamma.source (C.ladder.frontier S.index) := by
    rw [IsSeparatorFrom, C.ladder.frontier_eq_essential_terminalFrontier
      C.legal.roofsSourceAtStages S.index, Gamma.roof_essential]
    exact C.legal.roofsSourceAtStages (Ladder.Stage.toExtended S.index)
  have htrim := C.legal.frontiersEssential S.index
  have hquot := C.frontier_quotient_isUnhindered S.index_mem
  refine ⟨{
    targetPaths := P
    remainder := R
    stopover := C.ladder.frontier S.index
    targetPaths_isWarp := hP.isWarp
    targetPaths_finite := hP.finiteCharacter
    targetPaths_card := (ColouredSafeShortcutGraph.mk_paths_le_vertexSet hP.isWarp).trans hPcard
    targetPaths_initial_subset_source := hsource
    designated_initial := hdesignated
    targetPaths_terminal_target := hP.terminalFrontier_subset
    targetPaths_carrier_roof := hroof
    targetPaths_link_designated := hlinks A0 hA0source hdesignated
    remainder_isWarp := carrierReferenceRemainder.isWarp C.ladder S.index _ C.legal
    remainder_finite := carrierReferenceRemainder.finiteCharacter C.ladder S.index _
    remainder_initial_subset_source := carrierReferenceRemainder.initialSet_subset_source
      C.ladder S.index _
    remainder_terminal_stopover := carrierReferenceRemainder.terminalFrontier_subset
      C.ladder S.index _ C.legal
    remainder_endpointPure := carrierReferenceRemainder.endpointPure
      C.ladder S.index _ C.legal C.normalized
    families_disjoint := carrierReferenceRemainder.disjoint_family C.ladder S.index _ Set.Subset.rfl
    source_cover := carrierReferenceRemainder.initialSet_cover C.ladder S.index _
      C.legal hsource hcover
    stopover_separator := hseparator
    stopover_trimmed := htrim
    protected_quotient_unhindered := Gamma.delete_quotient_isUnhindered_of_subset_roof
      hroof htrim hseparator hquot
    height := DeferredHalfwayFrontierHeight.frontier_heightAtMost
      C.normalized C.legal C.capacity_infinite S.index
    remainder_terminalClean := carrierReferenceRemainder.terminalClean C.ladder S.index _ C.legal
    remainder_carrier_roof := carrierReferenceRemainder.vertexSet_subset_roof
      C.ladder S.index _ C.legal
    original_quotient_unhindered := hquot
    targetPaths_link_initial := hlinks (Gamma.initialSet P) hsource Set.Subset.rfl
  }⟩

#print axioms exists_localizedProtectedGeometry

end Erdos599.Blueprint.ColouredSafeEndpointBlueprint.StableState

namespace Erdos599.Blueprint.LinkageBlueprint.CausalSection9Rows

open Set Cardinal Order DirectedPath Ladder ColouredSafeEndpointBlueprint
open ColouredSafeEndpointBlueprint.StableState

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

/-- The protected half-way engine once its actual initial stable state has
been constructed. Neither final boundary data nor a fair history is assumed. -/
theorem exists_endpointProtectedHalfway
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hC : C.ladder = finalLadder Gamma kappa hkappa hGamma seed hseed)
    (hext : _root_.Erdos599.CardinalInduction.ProtectedCardinalAssembly.ExtensionThroughFor
      Gamma kappa) (hsub : HasHereditarySubdivisionIncidence Gamma.graph)
    (S : StableState C (globalCarrier Gamma kappa hkappa hGamma seed hseed))
    {A0 : Set V} (hA0source : A0 ⊆ Gamma.source) (hA0carrier : A0 ⊆ S.carrier) :
    Nonempty (CardinalInduction.LocalizedProtectedHalfwayGeometry Gamma A0 kappa) := by
  obtain ⟨U, hSU, hcomplete⟩ := exists_endpointFullyCompleted hkappa hGamma hseed C hC hext hsub S
  exact U.exists_localizedProtectedGeometry hcomplete hA0source (hA0carrier.trans hSU.vertices)

#print axioms exists_endpointProtectedHalfway

end Erdos599.Blueprint.LinkageBlueprint.CausalSection9Rows
