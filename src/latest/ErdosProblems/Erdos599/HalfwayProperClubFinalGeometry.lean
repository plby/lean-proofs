/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCofinalBlueprintRelation
import ErdosProblems.Erdos599.HalfwayClubFinalGeometry
import ErdosProblems.Erdos599.HalfwayExactFrontierClause

/-!
# Source-disjoint exact club frontiers

Definition 2.23 forms a quotient only at a vertex set disjoint from the
current source.  The older `IsHalfwayStopover` interface does not record
that typing condition.  This file therefore strengthens the exact-frontier
output used by the club scheduler and keeps source-disjointness attached to
the literal terminal frontier of the completed family.

No new construction premise is hidden here: the only additional field of
`ProperRankedClubFrontierBoundary` is the concrete geometric fact
`Disjoint Gamma.source C.newSlice`.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace CardinalInduction

open DirectedPath Blueprint Blueprint.LinkageBlueprint

universe u v

variable {V : Type u}

/-- Exact-frontier half-way output satisfying the quotient-domain condition
from Definition 2.23. -/
def ProperExactFrontierHalfwayLinkageOfAltitude
    (Gamma : DWeb V) (A0 : Set V) (kappa : Cardinal.{u})
    (W : Set Gamma.DPath) : Prop :=
  ∃ C : Set V, IsHalfwayStopover Gamma W C ∧
    Gamma.terminalFrontier W = C ∧ Disjoint Gamma.source C ∧
    LinksToTarget Gamma W A0 ∧ HeightAtMost Gamma C kappa

namespace ProperExactFrontierHalfwayLinkageOfAltitude

/-- Forgetting source-disjointness recovers the exact-frontier public
interface. -/
theorem toExactFrontier
    {Gamma : DWeb V} {A0 : Set V} {kappa : Cardinal.{u}}
    {W : Set Gamma.DPath}
    (h : ProperExactFrontierHalfwayLinkageOfAltitude Gamma A0 kappa W) :
    ExactFrontierHalfwayLinkageOfAltitude Gamma A0 kappa W := by
  obtain ⟨C, hC, hfrontier, _hdisjoint, hlinks, hheight⟩ := h
  exact ⟨C, hC, hfrontier, hlinks, hheight⟩

/-- In particular, the strengthened output is an ordinary qualified
half-way linkage. -/
theorem toHalfwayLinkageOfAltitude
    {Gamma : DWeb V} {A0 : Set V} {kappa : Cardinal.{u}}
    {W : Set Gamma.DPath}
    (h : ProperExactFrontierHalfwayLinkageOfAltitude Gamma A0 kappa W) :
    IsHalfwayLinkageOfAltitude Gamma A0 kappa W :=
  h.toExactFrontier.toHalfwayLinkageOfAltitude

end ProperExactFrontierHalfwayLinkageOfAltitude

/-- A resolved blueprint whose selected stopover avoids the ambient source
produces a literal completed family with the same proper frontier. -/
theorem GloballyResolvedBlueprintCertificate.exists_properExactFrontierHalfwayLinkage
    {Gamma : DWeb V} {A0 : Set V} {kappa : Cardinal.{u}}
    (C : GloballyResolvedBlueprintCertificate Gamma A0 kappa)
    (hdisjoint : Disjoint Gamma.source C.stopover) :
    ∃ W : Set Gamma.DPath,
      ProperExactFrontierHalfwayLinkageOfAltitude Gamma A0 kappa W := by
  let R : Set Gamma.DPath := C.blueprint.referenceRemainder C.slice
  let W : Set Gamma.DPath := C.blueprint.completedFamily C.edge_real R
  have hwarp : Gamma.IsWarp W :=
    C.blueprint.isWarp_completedFamily C.edge_real
      (C.blueprint.isWarp_referenceRemainder C.slice C.reference_isWarp)
      (C.blueprint.disjoint_referenceRemainder C.slice)
  have hUfinite : ∀ p ∈ C.blueprint.paths,
      ∃ q : FinitePath
        (Blueprint.imaginaryGraph Gamma C.reference kappa), p = .inl q := by
    intro p hp
    obtain ⟨q, hpq, -⟩ := C.blueprint_endpointPure p hp
    exact ⟨q, hpq⟩
  have hRfinite : Gamma.HasFiniteCharacter R := by
    intro p hp
    obtain ⟨q, hpq, -⟩ := C.reference_endpointPure p hp
    exact ⟨q, hpq⟩
  have hfinite : Gamma.HasFiniteCharacter W :=
    C.blueprint.finiteCharacter_completedFamily C.edge_real
      hUfinite hRfinite
  have hinitial : Gamma.initialSet W = Gamma.source := by
    rw [C.blueprint.initialSet_completedFamily C.edge_real R]
    exact C.source_cover
  have hterminal : Gamma.terminalFrontier W = C.stopover := by
    rw [C.blueprint.terminalFrontier_completedFamily C.edge_real R]
    exact C.terminal_frontier
  have hpure : ∀ p ∈ W,
      IsPathBetween Gamma Gamma.source C.stopover p :=
    C.blueprint.endpointPure_completedFamily C.edge_real
      C.blueprint_endpointPure C.reference_endpointPure
  have hlinkage : IsLinkageBetween Gamma Gamma.source C.stopover W :=
    ⟨hwarp, hfinite, hinitial, hterminal.le, hpure⟩
  have hgraph : C.blueprint.familyGraph = C.blueprint.realPart := by
    change Blueprint.FamilyGraph.mk C.blueprint.familyGraph.vertices
        C.blueprint.familyGraph.edges =
      Blueprint.FamilyGraph.mk C.blueprint.realPart.vertices
        C.blueprint.realPart.edges
    apply congrArg₂ (fun vertices edges ↦
      Blueprint.FamilyGraph.mk vertices edges)
    · rfl
    · change C.blueprint.familyGraph.edges =
        C.blueprint.familyGraph.edges ∩
          {e | Gamma.graph.Adj e.1 e.2}
      apply Set.Subset.antisymm
      · intro e he
        exact ⟨he, C.edge_real he⟩
      · exact Set.inter_subset_left
  have hterminalTarget : C.blueprint.terminalSet ⊆ Gamma.target := by
    intro x hx
    have hxterm := C.blueprint.terminalSet_subset_familyGraph_terminals
      C.blueprint_endpointPure hx
    rw [hgraph] at hxterm
    exact C.real_terminals_target hxterm
  have hblueprintLinks : C.blueprint.BlueprintLinksToTarget A0 :=
    C.blueprint.blueprintLinksToTarget_of_initial_terminal
      C.designated_source C.designated_initial C.blueprint_endpointPure
      hterminalTarget
  have hlinks : LinksToTarget Gamma W A0 :=
    C.blueprint.linksToTarget_completedFamily C.edge_real R hblueprintLinks
  have hheight : HeightAtMost Gamma C.stopover kappa :=
    ⟨C.heightDelete,
      ⟨C.heightDelete_nonSource, C.heightWave, C.heightWave_isWave,
        C.stopover_roofed⟩,
      C.heightDelete_card⟩
  exact ⟨W, C.stopover,
    ⟨hlinkage, C.stopover_separator, C.stopover_trimmed,
      C.quotient_unhindered⟩,
    hterminal, hdisjoint, hlinks, hheight⟩

end CardinalInduction

namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating

universe u v

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}} {I : Type v}
variable [Preorder I] [Nonempty I] [IsDirectedOrder I]

/-- The exact relation boundary together with the source-disjointness needed
to use the selected frontier as an actual quotient stopover. -/
structure ProperRankedClubFrontierBoundary
    (C : ClubStageGeometry Gamma Y kappa (Order.succ kappa))
    (R : CardinalInduction.HalfwayScheduler.RankedFairGlobalRelation
      Gamma Y kappa Gamma.target I)
    (A0 : Set V) : Prop where
  boundary :
    CardinalInduction.HalfwayScheduler.RankedClubFrontierBoundary C R A0
  source_disjoint : Disjoint Gamma.source C.newSlice

namespace CofinalBlueprintRelationRun

/-- A fair cofinal union of actual blueprint real parts, with a proper exact
club boundary, closes directly to a source-disjoint exact half-way output. -/
theorem exists_properExactFrontierHalfwayLinkage
    {C : ClubStageGeometry Gamma Y kappa (Order.succ kappa)}
    (R : CofinalBlueprintRelationRun Gamma Y kappa Gamma.target I)
    {A0 : Set V}
    (B : ProperRankedClubFrontierBoundary C R.rankedFairGlobalRelation A0) :
    ∃ W : Set Gamma.DPath,
      CardinalInduction.ProperExactFrontierHalfwayLinkageOfAltitude
        Gamma A0 kappa W := by
  obtain ⟨F, hFstop⟩ := B.boundary.exists_finalGeometry_at_frontier
  apply F.certificate.exists_properExactFrontierHalfwayLinkage
  change Disjoint Gamma.source F.stopover
  rw [hFstop]
  exact B.source_disjoint

/-- Proper output projects to the exact-frontier interface already consumed
by the public cardinal induction. -/
theorem exists_exactFrontierHalfwayLinkage_of_proper
    {C : ClubStageGeometry Gamma Y kappa (Order.succ kappa)}
    (R : CofinalBlueprintRelationRun Gamma Y kappa Gamma.target I)
    {A0 : Set V}
    (B : ProperRankedClubFrontierBoundary C R.rankedFairGlobalRelation A0) :
    ∃ W : Set Gamma.DPath,
      CardinalInduction.ExactFrontierHalfwayLinkageOfAltitude
        Gamma A0 kappa W := by
  obtain ⟨W, hW⟩ := R.exists_properExactFrontierHalfwayLinkage B
  exact ⟨W, hW.toExactFrontier⟩

end CofinalBlueprintRelationRun

#print axioms
  CardinalInduction.GloballyResolvedBlueprintCertificate.exists_properExactFrontierHalfwayLinkage
#print axioms
  CofinalBlueprintRelationRun.exists_properExactFrontierHalfwayLinkage

end LinkageBlueprint
end Blueprint
end Erdos599
