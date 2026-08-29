/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingFiniteFragment
import ErdosProblems.Erdos599.GroundingFragmentRelation
import ErdosProblems.Erdos599.GroundingRayFragment

/-!
# Partition of ladder paths by surviving fragments

This file assembles the finite-parent and ray-parent constructions of the
maximal components left after deleting `GroundingCut.CE`.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingFragmentPartition

open DirectedPath

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}

abbrev Input (Gamma : DWeb V) (I : Type v) : Type (max u v) :=
  PopularAuxiliary.Input Gamma I

abbrev LV (L : Input Gamma I) : Type (max u v) :=
  PopularAuxiliary.Input.LambdaVertex V I

/-- Every vertex of every ladder member lies on a maximal component left
after deleting the represented cut edges.  The component is a finite path
for a finite parent, and is either a finite segment or a ray tail for a ray
parent. -/
theorem exists_fragment_containing
    (L : Input Gamma I) (C : Set (LV L))
    {p : Gamma.DPath} (hp : p ∈ L.ladder.paths)
    {x : V} (hx : x ∈ p.support) :
    ∃ P : L.Fragment,
      P.parent = p ∧ P ∈ GroundingCut.fragments L C ∧
        x ∈ P.path.support := by
  cases p with
  | inl p =>
      exact GroundingFiniteFragment.exists_deletedFragment_through_finite
        L C p hp hx
  | inr r =>
      exact GroundingRayFragment.exists_ray_fragment_containing L C r hp hx

/-- Two supported vertices are in one maximal surviving fragment exactly
when the literal parent interval between them avoids the deleted edges. -/
theorem survivingConnected_iff_exists_common_fragment
    (L : Input Gamma I) (C : Set (LV L))
    {p : Gamma.DPath} (hp : p ∈ L.ladder.paths)
    {x y : V} (hx : x ∈ p.support) (hy : y ∈ p.support) :
    GroundingCut.SurvivingConnected L C p x y ↔
      ∃ P : L.Fragment,
        P.parent = p ∧ P ∈ GroundingCut.fragments L C ∧
          x ∈ P.path.support ∧ y ∈ P.path.support := by
  constructor
  · intro hxy
    obtain ⟨P, hparent, hP, hxP⟩ :=
      exists_fragment_containing L C hp hx
    have hiX : GroundingCut.SurvivingConnected L C P.parent
        P.path.initial x :=
      GroundingFragmentRelation.survivingConnected_of_mem_fragment
        hP P.path.initial_mem_support hxP
    have hXY : GroundingCut.SurvivingConnected L C P.parent x y := by
      simpa [hparent] using hxy
    have hiY : GroundingCut.SurvivingConnected L C P.parent
        P.path.initial y :=
      GroundingFragmentRelation.survivingConnected_trans
        L C P.parent hiX hXY
    have hyP : y ∈ P.path.support := by
      rw [hP.2]
      exact ⟨by simpa [hparent] using hy, hiY⟩
    exact ⟨P, hparent, hP, hxP, hyP⟩
  · rintro ⟨P, hparent, hP, hxP, hyP⟩
    have hxy :=
      GroundingFragmentRelation.survivingConnected_of_mem_fragment
        hP hxP hyP
    simpa [hparent] using hxy

/-- Members of the fragment family with the same parent and a common
vertex have the same support; this is the extensional uniqueness assertion
needed for the path partition. -/
theorem fragment_support_unique_of_common
    {L : Input Gamma I} {C : Set (LV L)} {P Q : L.Fragment}
    (hP : P ∈ GroundingCut.fragments L C)
    (hQ : Q ∈ GroundingCut.fragments L C)
    (hparent : P.parent = Q.parent) {x : V}
    (hxP : x ∈ P.path.support) (hxQ : x ∈ Q.path.support) :
    P.path.support = Q.path.support :=
  GroundingFragmentRelation.fragment_support_eq_of_parent_eq_of_common
    hP hQ hparent hxP hxQ

end GroundingFragmentPartition
end Erdos599
