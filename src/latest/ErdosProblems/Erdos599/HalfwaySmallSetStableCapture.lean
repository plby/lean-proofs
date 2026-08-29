/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayMovingGlobalClosureCapture

/-!
# Stabilizing a small set on later ladder frontiers

For each vertex choose a roofing stage, choosing a strict-roof stage for a
nonpersistent vertex. A common strict upper bound gives a later club stage
at which exactly the persistent vertices of the set are on the frontier.
The same equality holds at every later ordinary stage.
-/

noncomputable section

open Set Cardinal Order

namespace Erdos599.Blueprint.LinkageBlueprint.ClubStageGeometry

open Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- The fixed-set `gamma_x` step of Assertion 9.31, with exact frontier
stabilization on the entire tail. -/
theorem exists_stable_later_club
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (X : Set V) (hXcard : #X ≤ kappa) (hXroof : X ⊆ C.ladder.limitRoof) :
    ∃ a ∈ C.club, C.newStage < a ∧
      ∀ b : Ladder.Stage (succ kappa), a ≤ b →
        X ⊆ Gamma.roof (C.ladder.frontier b) ∧
        X ∩ C.ladder.frontier b = X ∩ C.persistent ∧
        X \ C.persistent ⊆ Gamma.strictRoof (C.ladder.frontier b) := by
  have hborn (x : X) : ∃ a : Ladder.Stage (succ kappa),
      x.1 ∈ Gamma.roof (C.ladder.frontier a) ∧
        (x.1 ∉ C.persistent → x.1 ∈ Gamma.strictRoof (C.ladder.frontier a)) := by
    by_cases hpersistent : x.1 ∈ C.persistent
    · obtain ⟨a, hxa⟩ := Set.mem_iUnion.1 (hXroof x.2)
      exact ⟨a, hxa, fun hnot ↦ (hnot hpersistent).elim⟩
    · have hxStrict : x.1 ∈ C.ladder.limitStrictRoof := by
        by_contra hxNotStrict
        exact hpersistent ⟨hXroof x.2, hxNotStrict⟩
      obtain ⟨a, hxa⟩ := Set.mem_iUnion.1 hxStrict
      exact ⟨a, hxa.1, fun _ ↦ hxa⟩
  let birth : X → Ladder.Stage (succ kappa) :=
    fun x ↦ Classical.choose (hborn x)
  have hbirth (x : X) :
      x.1 ∈ Gamma.roof (C.ladder.frontier (birth x)) ∧
        (x.1 ∉ C.persistent →
          x.1 ∈ Gamma.strictRoof (C.ladder.frontier (birth x))) :=
    Classical.choose_spec (hborn x)
  obtain ⟨upper, hupper⟩ :=
    Stationary.exists_strictUpperBound_of_mk_lt C.legal.regular birth
      (lt_succ_iff.mpr hXcard)
  let beta : Ladder.Stage (succ kappa) :=
    RegularCardinal.aboveInClub C.legal.regular C.club C.club_isClub
      C.newStage upper
  have hbetaClub : beta ∈ C.club :=
    RegularCardinal.aboveInClub_mem C.legal.regular C.club C.club_isClub
      C.newStage upper
  have hcurrentBeta : C.newStage < beta :=
    RegularCardinal.left_lt_aboveInClub C.legal.regular C.club C.club_isClub
      C.newStage upper
  have hupperBeta : upper < beta :=
    RegularCardinal.right_lt_aboveInClub C.legal.regular C.club C.club_isClub
      C.newStage upper
  refine ⟨beta, hbetaClub, hcurrentBeta, ?_⟩
  intro b hbetaB
  have hbirthB (x : X) : birth x < b :=
    (hupper x).trans (hupperBeta.trans_le hbetaB)
  have hroofB : X ⊆ Gamma.roof (C.ladder.frontier b) := by
    intro x hx
    exact Gamma.roof_cut (C.legal.frontierChronology (hbirthB ⟨x, hx⟩))
      (hbirth ⟨x, hx⟩).1
  have hnotFrontier (x : X) (hp : x.1 ∉ C.persistent) :
      x.1 ∉ C.ladder.frontier b :=
    Set.disjoint_left.1 (C.legal.strictFrontierChronology (hbirthB x))
      ((hbirth x).2 hp)
  have hfrontierEq : X ∩ C.ladder.frontier b = X ∩ C.persistent := by
    ext x
    constructor
    · rintro ⟨hx, hxb⟩
      refine ⟨hx, ?_⟩
      by_contra hnot
      exact hnotFrontier ⟨x, hx⟩ hnot hxb
    · rintro ⟨hx, hp⟩
      refine ⟨hx, ?_⟩
      have hxEssential : x ∈ Gamma.essential (C.ladder.frontier b) := by
        by_contra hxNotEssential
        exact hp.2 (Set.mem_iUnion.2 ⟨b, hroofB hx, hxNotEssential⟩)
      rwa [C.legal.frontiersEssential b] at hxEssential
  refine ⟨hroofB, hfrontierEq, ?_⟩
  rintro x ⟨hx, hp⟩
  refine ⟨hroofB hx, ?_⟩
  rw [C.legal.frontiersEssential b]
  exact hnotFrontier ⟨x, hx⟩ hp

#print axioms exists_stable_later_club

end Erdos599.Blueprint.LinkageBlueprint.ClubStageGeometry
