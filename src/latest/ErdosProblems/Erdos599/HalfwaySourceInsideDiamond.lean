/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwaySourceInsideClubCompatibility
import ErdosProblems.Erdos599.HalfwaySourceWarpDiamondFresh

/-!
# The concrete inside diamond in Assertion 9.31

For the later-stage target row `W` and the closed set `X`, Assertion 9.31
first forms the literal inside restriction `W[X]` and then the source
diamond `current \diamond W[X]`.  The club-stage roof geometry proves the
compatibility internally.  In particular, the resulting family contains
the whole current carrier and edge relation, while every edge entering the
current carrier was already current.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y Z : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace SourceInsideRestriction

/-- The paper's concrete `current \diamond W[X]`, with compatibility
discharged from the later club-stage linkage and the old roof. -/
def clubStageDiamond
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (current : LinkageBlueprint Gamma Z kappa) {A X : Set V}
    (hCurrentRoof : current.vertexSet ⊆ C.outerRoof)
    (hCurrentTerminal : current.terminalSet = A)
    {P : Set (C.ladder.stageWeb C.newStage).DPath}
    (hA : A ⊆ C.newSlice)
    (hP : CardinalInduction.IsLinkageBetween
      (C.ladder.stageWeb C.newStage) A
        (C.ladder.stageWeb C.newStage).target P)
    (I : SourceInsideRestriction (Y := Z) (kappa := kappa)
      (CardinalInduction.SliceSegmentCore.liftStageFamily
        C.ladder C.newStage P) X) :
    LinkageBlueprint Gamma Z kappa :=
  sourceWarpDiamond current I.family
    (I.starCompatible_of_clubStageRow C current hCurrentRoof
      hCurrentTerminal hA hP)

variable
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (current : LinkageBlueprint Gamma Z kappa) {A X : Set V}
    (hCurrentRoof : current.vertexSet ⊆ C.outerRoof)
    (hCurrentTerminal : current.terminalSet = A)
    {P : Set (C.ladder.stageWeb C.newStage).DPath}
    (hA : A ⊆ C.newSlice)
    (hP : CardinalInduction.IsLinkageBetween
      (C.ladder.stageWeb C.newStage) A
        (C.ladder.stageWeb C.newStage).target P)
    (I : SourceInsideRestriction (Y := Z) (kappa := kappa)
      (CardinalInduction.SliceSegmentCore.liftStageFamily
        C.ladder C.newStage P) X)

@[simp] theorem clubStageDiamond_vertexSet :
    (I.clubStageDiamond C current hCurrentRoof hCurrentTerminal hA hP).vertexSet =
      current.vertexSet ∪
        (Gamma.vertexSet
          (CardinalInduction.SliceSegmentCore.liftStageFamily
            C.ladder C.newStage P) ∩ X) := by
  rw [clubStageDiamond, vertexSet_sourceWarpDiamond, I.family_vertexSet]

@[simp] theorem clubStageDiamond_edgeSet :
    (I.clubStageDiamond C current hCurrentRoof hCurrentTerminal hA hP).edgeSet =
      current.edgeSet ∪
        (familyEdges
          (CardinalInduction.SliceSegmentCore.liftStageFamily
            C.ladder C.newStage P) ∩ (X ×ˢ X)) := by
  rw [clubStageDiamond,
    edgeSet_sourceWarpDiamond current I.family I.finiteCharacter,
    I.family_edgeSet]

/-- The inside diamond is finite-character whenever the current family is.
The later inside row is finite by construction. -/
theorem clubStageDiamond_finiteCharacter
    (hCurrentFinite : (imaginaryWeb Gamma Z kappa).HasFiniteCharacter
      current.paths) :
    (imaginaryWeb Gamma Z kappa).HasFiniteCharacter
      (I.clubStageDiamond C current hCurrentRoof hCurrentTerminal hA hP).paths :=
  (imaginaryWeb Gamma Z kappa).hasFiniteCharacter_warpDiamond
    hCurrentFinite I.finiteCharacter
      (I.starCompatible_of_clubStageRow C current hCurrentRoof
        hCurrentTerminal hA hP)

theorem current_vertexSet_subset_clubStageDiamond :
    current.vertexSet ⊆
      (I.clubStageDiamond C current hCurrentRoof hCurrentTerminal hA hP).vertexSet := by
  rw [I.clubStageDiamond_vertexSet C current hCurrentRoof
    hCurrentTerminal hA hP]
  exact Set.subset_union_left

theorem current_edgeSet_subset_clubStageDiamond :
    current.edgeSet ⊆
      (I.clubStageDiamond C current hCurrentRoof hCurrentTerminal hA hP).edgeSet := by
  rw [I.clubStageDiamond_edgeSet C current hCurrentRoof
    hCurrentTerminal hA hP]
  exact Set.subset_union_left

/-- Exact fresh-incidence conclusion for the actual inside diamond: no
new inside-row edge enters the current carrier. -/
theorem clubStageDiamond_noNewIncomingCurrent :
    ∀ {x y : V}, x ∈ current.vertexSet →
      (y, x) ∈
        (I.clubStageDiamond C current hCurrentRoof hCurrentTerminal hA hP).edgeSet →
      (y, x) ∈ current.edgeSet := by
  exact sourceWarpDiamond_noNewIncomingOld current I.family I.finiteCharacter
    (I.starCompatible_of_clubStageRow C current hCurrentRoof
      hCurrentTerminal hA hP)

theorem clubStageDiamond_fresh_noIncomingCurrent :
    ∀ {x y : V}, x ∈ current.vertexSet →
      (y, x) ∈
        (I.clubStageDiamond C current hCurrentRoof hCurrentTerminal hA hP).edgeSet \
          current.edgeSet → False := by
  intro x y hx hyx
  exact hyx.2 (I.clubStageDiamond_noNewIncomingCurrent C current
    hCurrentRoof hCurrentTerminal hA hP hx hyx.1)

/-- Source coverage is inherited from the current family without any
assumption on the initials of the later row. -/
theorem source_subset_clubStageDiamond_initialSet
    (hsource : Gamma.source ⊆ current.initialSet) :
    Gamma.source ⊆
      (I.clubStageDiamond C current hCurrentRoof hCurrentTerminal hA hP).initialSet :=
  sourceWarpDiamond_covers_source current I.family
    (I.starCompatible_of_clubStageRow C current hCurrentRoof
      hCurrentTerminal hA hP) hsource

#print axioms clubStageDiamond
#print axioms clubStageDiamond_edgeSet
#print axioms clubStageDiamond_noNewIncomingCurrent
#print axioms source_subset_clubStageDiamond_initialSet

end SourceInsideRestriction
end Erdos599.Blueprint.LinkageBlueprint
