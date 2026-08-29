/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LadderRoofRecursion
import ErdosProblems.Erdos599.Normalization
import ErdosProblems.Erdos599.SingularCardinal

/-!
# Row-local closure operations for the regular-cardinal construction

This module contains the small graph-theoretic operations used by both the
causal row recursion and its final consumer.  Keeping them below
`RegularRows` avoids an import cycle between that recursion and
`RegularExtension`.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction

open DirectedPath

universe u

variable {V : Type u}

namespace RegularExtension

variable (G : DWeb V)

/-- Every causal prefix of the canonical ladder is a warp. -/
theorem canonicalLadderCore_warpAt_isWarp_of_normalized
    (hG : G.IsNormalized) (kappa : Cardinal.{u})
    (preferred : Ladder.Stage kappa -> Option V) (a : Ladder.Stage kappa) :
    G.IsWarp ((G.canonicalLadderCore kappa preferred).warpAt a) := by
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hG hxy).1 hy
  have hgeometry := DWeb.KappaLadder.canonicalLadder_geometry
    (G := G) preferred hNoEnter
  exact hgeometry.warpStages (Ladder.Stage.toExtended a)

/-- Members of `F` which meet a vertex set `S`. -/
def pathsMeeting (F : Set G.DPath) (S : Set V) : Set G.DPath :=
  {p | p ∈ F ∧ (p.support ∩ S).Nonempty}

@[simp]
theorem mem_pathsMeeting {F : Set G.DPath} {S : Set V} {p : G.DPath} :
    p ∈ pathsMeeting G F S ↔ p ∈ F ∧ (p.support ∩ S).Nonempty :=
  Iff.rfl

private theorem pathsMeeting_eq_singular_pathsMeeting
    (F : Set G.DPath) (S : Set V) :
    pathsMeeting G F S =
      {p | p ∈ F ∧ ¬ Disjoint p.support S} := by
  ext p
  constructor
  · rintro ⟨hpF, x, hxp, hxS⟩
    exact ⟨hpF, Set.not_disjoint_iff.2 ⟨x, hxp, hxS⟩⟩
  · rintro ⟨hpF, hpS⟩
    obtain ⟨x, hxp, hxS⟩ := Set.not_disjoint_iff.1 hpS
    exact ⟨hpF, x, hxp, hxS⟩

/-- The new vertices contributed by all members of a warp meeting one
bounded row are bounded by the same infinite cardinal. -/
theorem mk_vertexSet_pathsMeeting_le_of_warp
    {F : Set G.DPath} {S : Set V} {kappa : Cardinal.{u}}
    (hkappa : aleph0 <= kappa) (hFwarp : G.IsWarp F)
    (hS : #S <= kappa) :
    #(G.vertexSet (pathsMeeting G F S)) <= kappa := by
  have hpaths : #(pathsMeeting G F S) <= kappa := by
    rw [pathsMeeting_eq_singular_pathsMeeting G F S]
    exact (G.mk_pathsMeeting_le F S hFwarp).trans hS
  by_cases hnonempty : (pathsMeeting G F S).Nonempty
  · letI : Nonempty (pathsMeeting G F S) := hnonempty.to_subtype
    have heq : G.vertexSet (pathsMeeting G F S) =
        ⋃ p : pathsMeeting G F S, p.1.support := by
      ext x
      simp only [DWeb.vertexSet, Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨p, hp, hxp⟩
        exact ⟨⟨p, hp⟩, hxp⟩
      · rintro ⟨p, hxp⟩
        exact ⟨p.1, p.2, hxp⟩
    rw [heq]
    refine (Cardinal.mk_iUnion_le
      (fun p : pathsMeeting G F S => p.1.support)).trans ?_
    apply Cardinal.mul_le_of_le hkappa hpaths
    apply ciSup_le
    intro p
    exact p.1.support_countable.le_aleph0.trans hkappa
  · have hempty : pathsMeeting G F S = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hnonempty
    rw [hempty, DWeb.vertexSet]
    simp

/-- The two ambient path-closure contributions made from one earlier row. -/
def twoWarpRowRegistration (F Y : Set G.DPath) (S : Set V) : Set V :=
  G.vertexSet (pathsMeeting G F S) ∪
    G.vertexSet (pathsMeeting G Y S)

theorem mk_twoWarpRowRegistration_le
    {F Y : Set G.DPath} {S : Set V} {kappa : Cardinal.{u}}
    (hkappa : aleph0 <= kappa) (hF : G.IsWarp F) (hY : G.IsWarp Y)
    (hS : #S <= kappa) :
    #(twoWarpRowRegistration G F Y S) <= kappa := by
  apply (Cardinal.mk_union_le _ _).trans
  exact Cardinal.add_le_of_le hkappa
    (mk_vertexSet_pathsMeeting_le_of_warp G hkappa hF hS)
    (mk_vertexSet_pathsMeeting_le_of_warp G hkappa hY hS)

theorem vertexSet_pathsMeeting_left_subset_twoWarpRowRegistration
    (F Y : Set G.DPath) (S : Set V) :
    G.vertexSet (pathsMeeting G F S) ⊆
      twoWarpRowRegistration G F Y S :=
  Set.subset_union_left

theorem vertexSet_pathsMeeting_right_subset_twoWarpRowRegistration
    (F Y : Set G.DPath) (S : Set V) :
    G.vertexSet (pathsMeeting G Y S) ⊆
      twoWarpRowRegistration G F Y S :=
  Set.subset_union_right

end RegularExtension
end CardinalInduction
end Erdos599
