/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeNativeWholeOwnerTransaction
import ErdosProblems.Erdos599.HalfwayMovingGlobalReferenceRoof

/-!
# Reclosing the native whole-owner row

The changed alternating component need not belong to the closed set used to
construct the original interval transaction.  It is nevertheless small and
roofed.  We may therefore put it into a *new* native closing seed.  In the
resulting closure the whole-owner normalized row is closed under paths:
changed members are wholly in the seed, while unchanged members are literal
subpaths of limiting-reference owners.

This is intentionally not an assertion that the old row already reaches the
new closure's later frontier.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath
open _root_.Erdos599.Alternating
open _root_.Erdos599.CardinalInduction
open _root_.Erdos599.CardinalInduction.SliceCandidate
open ColouredSafeMovingStages

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {seed : Set V} {z : V} {R : LimitClosure C seed}

namespace NativePostClosureIntervalTransaction

/-- The fresh closing seed contains the old closed set and the entire
alternating component changed by normalization. -/
def nativeWholeOwnerClosingSeed
    (T : NativePostClosureIntervalTransaction C seed z R) : Set V :=
  R.closedSet ∪ T.nativeWholeOwnerComponent

/-- Alternating reachability stays inside any set containing the roots and
the carriers of both path families. -/
private theorem exceptionalComponentVertices_subset
    {W O : Set Gamma.DPath} {E A : Set V}
    (hE : E ⊆ A) (hW : Gamma.vertexSet W ⊆ A)
    (hO : Gamma.vertexSet O ⊆ A) :
    exceptionalComponentVertices Gamma W O E ⊆ A := by
  intro x hx
  simp only [exceptionalComponentVertices, Set.mem_iUnion] at hx
  obtain ⟨root, hrootE, hreach⟩ := hx
  change Relation.ReflTransGen
    (AlternatingComponents.EdgeRel W O) root x at hreach
  induction hreach with
  | refl => exact hE hrootE
  | @tail a b _hab hab ih =>
      rcases AlternatingComponents.edgeRel_implies_sameWarpPath hab with
        hsame | hsame
      · obtain ⟨p, hpW, _ha, hb⟩ := hsame
        exact hW ⟨p, hpW, hb⟩
      · obtain ⟨p, hpO, _ha, hb⟩ := hsame
        exact hO ⟨p, hpO, hb⟩

/-- The component added to the new seed remains in the captured stage roof. -/
theorem nativeWholeOwnerComponent_subset_capturedRoof
    (T : NativePostClosureIntervalTransaction C seed z R) :
    T.nativeWholeOwnerComponent ⊆
      (nativeCapturedGeometry R).outerRoof := by
  apply exceptionalComponentVertices_subset
  · exact T.nativeWholeOwnerSeed_subset_exceptionalComponents.trans
      T.interval.exceptionalComponents_subset_outerRoof
  · intro x hx
    obtain ⟨p, hp, hxp⟩ := hx
    exact T.interval.ambientInterval_in_outerRoof p hp hxp
  · exact T.nativeIntervalReference_vertices_subset_capturedRoof

/-- Every captured stage roof is one summand of the limiting roof. -/
theorem capturedRoof_subset_limitRoof
    (T : NativePostClosureIntervalTransaction C seed z R) :
    (nativeCapturedGeometry R).outerRoof ⊆ C.ladder.limitRoof := by
  intro x hx
  apply Set.mem_iUnion.2
  exact ⟨R.later.stage, hx⟩

theorem nativeWholeOwnerClosingSeed_card_le
    (T : NativePostClosureIntervalTransaction C seed z R) :
    #T.nativeWholeOwnerClosingSeed ≤ kappa := by
  refine (Cardinal.mk_union_le R.closedSet
    T.nativeWholeOwnerComponent).trans ?_
  exact Cardinal.add_le_of_le C.capacity_infinite R.card_le
    T.nativeWholeOwnerComponent_card_le

theorem nativeWholeOwnerClosingSeed_subset_limitRoof
    (T : NativePostClosureIntervalTransaction C seed z R) :
    T.nativeWholeOwnerClosingSeed ⊆ C.ladder.limitRoof := by
  exact Set.union_subset R.subset_limitRoof
    (T.nativeWholeOwnerComponent_subset_capturedRoof.trans
      T.capturedRoof_subset_limitRoof)

/-- Members retained from the completed row on the changed side are wholly
inside the changed component. -/
theorem nativeWholeOwner_left_support_subset_component
    (T : NativePostClosureIntervalTransaction C seed z R)
    {p : Gamma.DPath}
    (hp : p ∈ initialPart Gamma T.interval.ambientInterval
      T.nativeWholeOwnerComponent) :
    p.support ⊆ T.nativeWholeOwnerComponent := by
  exact path_support_subset_exceptionalComponents_left
    T.interval.ambientInterval_linkage.finiteCharacter hp.1
      p.initial_mem_support hp.2

/-- Once the changed component is included in a new reference-closed set,
the normalized row is itself closed under paths. -/
theorem nativeWholeOwnerInterval_closedUnderPaths_of_component_subset
    (T : NativePostClosureIntervalTransaction C seed z R)
    {X : Set V} (hcomponent : T.nativeWholeOwnerComponent ⊆ X)
    (hreference : ClosedUnderPaths Gamma C.ladder.limitWarp X) :
    ClosedUnderPaths Gamma T.nativeWholeOwnerInterval X := by
  intro p hp hmeet
  rcases hp with hpLeft | hpRight
  · exact T.nativeWholeOwner_left_support_subset_component hpLeft |>.trans
      hcomponent
  · let q : T.intervalReference := ⟨p, hpRight.1⟩
    obtain ⟨x, hxp, hxX⟩ := hmeet
    have howner : (T.intervalReferenceOwner q).support ⊆ X :=
      hreference (T.intervalReferenceOwner q)
        (T.intervalReferenceOwner_mem q)
        ⟨x, (T.intervalReference_subpath_owner q).1 hxp, hxX⟩
    exact (T.intervalReference_subpath_owner q).1.trans howner

/-- Reclose after whole-owner normalization.  The output is a genuine new
native limit closure, and the old normalized interval row is path-closed in
its carrier. -/
theorem exists_reclosed_wholeOwnerInterval
    (T : NativePostClosureIntervalTransaction C seed z R) :
    ∃ R' : LimitClosure C T.nativeWholeOwnerClosingSeed,
      R.later.stage < R'.later.stage ∧
        ClosedUnderPaths Gamma T.nativeWholeOwnerInterval R'.closedSet := by
  obtain ⟨R', hlater⟩ := LimitClosure.exists_of_seed_above C
    T.nativeWholeOwnerClosingSeed
    R.later.stage
    T.nativeWholeOwnerClosingSeed_card_le
    T.nativeWholeOwnerClosingSeed_subset_limitRoof
  refine ⟨R', hlater,
    T.nativeWholeOwnerInterval_closedUnderPaths_of_component_subset
      ?_ R'.reference_closed⟩
  intro x hx
  exact R'.seed_subset (Or.inr hx)

/-- Full handoff form: the new closure contains both the old closed set and
the changed component, while the literal selected front/path and tail
intersection of the old normalized row remain unchanged.  No assertion is
made here that this old row reaches `R'.later.stage`. -/
theorem exists_reclosed_wholeOwnerTransaction
    (T : NativePostClosureIntervalTransaction C seed z R) :
    ∃ R' : LimitClosure C T.nativeWholeOwnerClosingSeed,
      R.later.stage < R'.later.stage ∧
      R.closedSet ⊆ R'.closedSet ∧
      T.nativeWholeOwnerComponent ⊆ R'.closedSet ∧
      ClosedUnderPaths Gamma T.nativeWholeOwnerInterval R'.closedSet ∧
      (Sum.inl T.interval.front : Gamma.DPath) ∈
        T.nativeWholeOwnerInterval ∧
      (Sum.inl T.interval.path : Gamma.DPath) ∈
        (T.safe.toNativeCaptured R).ambientFamily ∧
      Gamma.vertexSet T.nativeWholeOwnerInterval ∩
          T.interval.tail.support = {T.interval.front.finish} := by
  obtain ⟨R', hlater, hclosed⟩ := T.exists_reclosed_wholeOwnerInterval
  refine ⟨R', hlater, ?_, ?_, hclosed,
    T.front_mem_nativeWholeOwnerInterval, ?_,
    T.nativeWholeOwnerInterval_tail_inter⟩
  · intro x hx
    exact R'.seed_subset (Or.inl hx)
  · intro x hx
    exact R'.seed_subset (Or.inr hx)
  · rw [← T.interval_safe_eq]
    exact T.interval.path_mem_safe

#print axioms NativePostClosureIntervalTransaction.nativeWholeOwnerComponent_subset_capturedRoof
#print axioms NativePostClosureIntervalTransaction.nativeWholeOwnerClosingSeed_card_le
#print axioms NativePostClosureIntervalTransaction.nativeWholeOwnerInterval_closedUnderPaths_of_component_subset
#print axioms NativePostClosureIntervalTransaction.exists_reclosed_wholeOwnerInterval
#print axioms NativePostClosureIntervalTransaction.exists_reclosed_wholeOwnerTransaction

end NativePostClosureIntervalTransaction
end Erdos599.Blueprint.LinkageBlueprint
