/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingFragmentSplice
import ErdosProblems.Erdos599.GroundingFragmentThinning

/-!
# Assertion 8.20: hanging-fragment collisions are nonstationary

Assume that the exact hanging-fragment collision subfan for one request has
stationary initial-index set.  First-hit owner thinning retains a stationary
set of indices whose chosen fragment pieces have distinct parent ladder
paths.  The deleted-predecessor splices for those retained paths are then
pairwise disjoint and end in the popular cut.  Their source-index set still
contains the retained stationary set, making the cut strongly popular.  This
contradicts the defining property of the popular separator.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace GroundingFragmentAssertion820

open DirectedPath Stationary
open PopularGroundingBridge

universe u

variable {V I : Type u} {Gamma : DWeb V}

abbrev Input (Gamma : DWeb V) (I : Type u) :=
  PopularAuxiliary.Input Gamma I

/-- Source-faithful Assertion 8.20.  No extra collision-selection or splice
hypothesis is needed: both are constructed from the exact collision
predicate and the failure of strong popularity of the separator. -/
theorem hangingFragmentWarpData
    {L : Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) :
    GroundingConcreteControls.HangingFragmentWarpData S := by
  refine { initialIndices_nonstationary := ?_ }
  intro r hstationary
  change IsStationaryBelow kappa
    (GroundingFragmentThinning.collisionIndices S r) at hstationary
  obtain ⟨B, hBsubset, hBstationary, hownerInj⟩ :=
    GroundingFragmentThinning.exists_stationary_firstHitParent_transversal
      S r hstationary
  let d : (j : B) →
      GroundingFragmentThinning.FirstHitOwner S r (j : Below kappa) :=
    fun j ↦ Classical.choose
      (GroundingFragmentThinning.firstHitOwner?_eq_some_of_mem S r
        (hBsubset j.property))
  have hd (j : B) :
      GroundingFragmentThinning.firstHitOwner? S r (j : Below kappa) =
        some (d j) := by
    exact Classical.choose_spec
      (GroundingFragmentThinning.firstHitOwner?_eq_some_of_mem S r
        (hBsubset j.property))
  let p : B → FinitePath L.lambda.graph := fun j ↦ (d j).path
  have hpCollision (j : B) :
      p j ∈ (GroundingFragmentThinning.collisionFan S r).paths := by
    exact (d j).path_mem
  have hp (j : B) : p j ∈ (requestFan S r).paths :=
    (hpCollision j).1
  have hmeet (j : B) :
      (p j).walk.Meets (GroundingFragmentCarrier.carrier S r) :=
    GroundingFragmentCarrier.collision_meets_carrier
      S r (hpCollision j).2
  have hfinish (j : B) :
      ((p j).firstHit (GroundingFragmentCarrier.carrier S r)
        (hmeet j)).finish ∈ (d j).piece.carrier := by
    exact (d j).firstHit_finish_mem_piece
  have hindex (j : B) :
      U.f ⟨(p j).start, (requestFan S r).starts_in_source (hp j)⟩ =
        (j : Below kappa) := by
    have hs :
        (⟨(p j).start, (requestFan S r).starts_in_source (hp j)⟩ :
          L.lambda.source) =
        ⟨(d j).path.start,
          (GroundingFragmentThinning.collisionFan S r).starts_in_source
            (d j).path_mem⟩ := by
      exact Subtype.ext rfl
    exact (congrArg U.f hs).trans (d j).index_eq
  have hpinj : Function.Injective p := by
    intro j k hjk
    apply Subtype.ext
    have hs :
        (⟨(p j).start, (requestFan S r).starts_in_source (hp j)⟩ :
          L.lambda.source) =
        ⟨(p k).start, (requestFan S r).starts_in_source (hp k)⟩ := by
      apply Subtype.ext
      exact congrArg FinitePath.start hjk
    exact (hindex j).symm.trans ((congrArg U.f hs).trans (hindex k))
  have hparentInj : Function.Injective
      (fun j : B ↦ (d j).piece.fragment.parent) := by
    intro j k hjk
    apply Subtype.ext
    apply hownerInj j.property k.property
    simp only [GroundingFragmentThinning.firstHitParent?, hd j, hd k]
    exact congrArg some hjk
  let W : Popular.XSWarp L.lambda S.cut :=
    GroundingFragmentSplice.selectedSpliceWarp
      S r p hp hpinj hmeet (fun j ↦ (d j).piece) hfinish hparentInj
  apply S.not_strongly_popular
  refine ⟨W, hBstationary.mono ?_⟩
  intro a ha
  let j : B := ⟨a, ha⟩
  have hj := GroundingFragmentSplice.index_mem_selectedSpliceWarp
    S r p hp hpinj hmeet (fun j ↦ (d j).piece) hfinish hparentInj j
  change U.f
      ⟨(p j).start, (requestFan S r).starts_in_source (hp j)⟩ ∈
    Popular.initialIndicesOf U W.paths W.starts_in_source at hj
  rw [hindex j] at hj
  exact hj

end GroundingFragmentAssertion820
end Erdos599

#print axioms Erdos599.GroundingFragmentAssertion820.hangingFragmentWarpData
