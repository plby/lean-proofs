/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GlobalBlueprintReplacement
import ErdosProblems.Erdos599.DeferredRegularGeometry

/-!
# The retained club-stage geometry

This is the geometric core used by the half-way linkage construction.  It
contains the two ladder stages, the causal closing family, and the exact
rung hypothesis needed to turn avoidance of the ladder obstruction into
unhinderedness of the selected quotient stages.

The rung hypothesis is deliberately explicit.  It is true for the canonical
ladder, but it is not a field of `KappaLadder.IsLegal` for arbitrary raw
ladder data.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating Ladder

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa theta : Cardinal.{u}}

/-- The safety premise used by the closing-up construction: every safe
alternating path lies in the displayed ordinary roof.  The preceding set
and strict roof determine which hammocks are eligible, but containment of a
chosen hammock follows from this uniform safe-path statement. -/
abbrev EligibleHammocksContainedInRoof
    (Gamma : DWeb V) (Y : Set Gamma.DPath)
    (_before _innerRoof outerRoof : Set V) : Prop :=
  ∀ Q : AltPath Gamma.graph, IsSafe Y Q → Q.vertexSet ⊆ outerRoof

/-- The union of the closed sets constructed strictly before a ladder
stage. -/
def closedBefore (closedStage : Ladder.Stage theta → Set V)
    (beta : Ladder.Stage theta) : Set V :=
  {x | ∃ alpha : Ladder.Stage theta,
    alpha < beta ∧ x ∈ closedStage alpha}

@[simp] theorem mem_closedBefore
    {closedStage : Ladder.Stage theta → Set V}
    {beta : Ladder.Stage theta} {x : V} :
    x ∈ closedBefore closedStage beta ↔
      ∃ alpha : Ladder.Stage theta,
        alpha < beta ∧ x ∈ closedStage alpha :=
  Iff.rfl

/-- A pair of club stages and the bounded increasing closing-up family used
between them.  `hindranceRungs` is the exact canonical-rung fact required
by Lemma 7.6; it is intentionally not inferred from bare legality. -/
structure ClubStageGeometry
    (Gamma : DWeb V) (Y : Set Gamma.DPath)
    (kappa theta : Cardinal.{u}) where
  ladder : Gamma.KappaLadder theta
  legal : DWeb.KappaLadder.Deferred.HalfwayGeometry ladder
  hindranceRungs : ∀ a, ¬ (ladder.stageWeb a).IsUnhindered →
    (ladder.stageWeb a).IsHindrance (ladder.rung a)
  hindranceObstruction : ladder.phiHindrance ⊆
    DWeb.KappaLadder.Deferred.phi ladder
  normalized : Gamma.IsNormalized
  club : Set (Ladder.Stage theta)
  club_isClub : Stationary.IsClubBelow theta club
  club_avoids_phi : Disjoint club
    (DWeb.KappaLadder.Deferred.phi ladder)
  oldStage : Ladder.Stage theta
  newStage : Ladder.Stage theta
  old_mem_club : oldStage ∈ club
  new_mem_club : newStage ∈ club
  old_lt_new : oldStage < newStage
  closedStage : Ladder.Stage theta → Set V
  closedStage_mono : ∀ {a b}, a ≤ b → closedStage a ⊆ closedStage b
  before_card : #(closedBefore closedStage newStage) ≤ kappa
  capacity_infinite : aleph0 ≤ kappa

namespace ClubStageGeometry

variable (C : ClubStageGeometry Gamma Y kappa theta)

/-- The slice at which the incoming blueprint lives. -/
abbrev oldSlice : Set V := C.ladder.frontier C.oldStage

/-- The later slice at which the replacement blueprint is certified. -/
abbrev newSlice : Set V := C.ladder.frontier C.newStage

/-- The strict roof in the hammock eligibility condition. -/
abbrev innerRoof : Set V := Gamma.strictRoof C.newSlice

/-- The ordinary roof which contains all objects of the transaction. -/
abbrev outerRoof : Set V := Gamma.roof C.newSlice

/-- The stage of the global closed set available to the transaction. -/
abbrev closedSet : Set V := C.closedStage C.newStage

/-- The cumulative closed set strictly before the later stage. -/
abbrev before : Set V := closedBefore C.closedStage C.newStage

/-- Vertices surviving on every sufficiently late ladder frontier. -/
abbrev persistent : Set V :=
  C.ladder.limitRoof \ C.ladder.limitStrictRoof

/-- Earlier closed stages lie in the selected later closed set. -/
theorem before_subset_closedSet : C.before ⊆ C.closedSet := by
  rintro x ⟨a, ha, hxa⟩
  exact C.closedStage_mono ha.le hxa

/-- Every stage in the avoiding club is unhindered. -/
theorem stageWeb_isUnhindered {a : Ladder.Stage theta}
    (ha : a ∈ C.club) : (C.ladder.stageWeb a).IsUnhindered := by
  intro hhindered
  obtain ⟨W, hW⟩ := hhindered
  have hrung :
      (C.ladder.stageWeb a).IsHindrance (C.ladder.rung a) :=
    C.hindranceRungs a (fun hstage ↦ hstage ⟨W, hW⟩)
  have hphi : a ∈ DWeb.KappaLadder.Deferred.phi C.ladder :=
    C.hindranceObstruction hrung
  exact Set.disjoint_left.1 C.club_avoids_phi ha hphi

theorem oldStage_isUnhindered :
    (C.ladder.stageWeb C.oldStage).IsUnhindered :=
  C.stageWeb_isUnhindered C.old_mem_club

theorem newStage_isUnhindered :
    (C.ladder.stageWeb C.newStage).IsUnhindered :=
  C.stageWeb_isUnhindered C.new_mem_club

end ClubStageGeometry
end LinkageBlueprint
end Blueprint
end Erdos599
