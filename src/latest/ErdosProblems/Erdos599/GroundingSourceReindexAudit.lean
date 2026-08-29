/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingWeakChronology

/-!
# Why successor reindexing does not repair Assertion 8.12

The bookkeeping used by the concrete ladder records a path at stage `a`
from the inessential part of the successor warp.  One tempting repair of the
printed strict chronology is therefore to give that source the successor
index `a + 1`.  This file records the precise obstruction to that repair.

For a regular uncountable cardinal, the range of any injective map which
moves every ordinal strictly upwards is nonstationary.  Indeed, its inverse
on the range is a regressive injection, contradicting Fodor's lemma.  In
particular the successor-stage map, and every source-index map which factors
through it, loses the stationary-range field required by the popular-layer
argument.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Stationary

universe u v

/-- An injective pointwise-upward reindexing of ordinals below a regular
uncountable cardinal has nonstationary range.  This is the abstract Fodor
obstruction behind the failure of successor reindexing. -/
theorem range_not_stationary_of_injective_lt
    {kappa : Cardinal.{u}} (hregular : kappa.IsRegular)
    (huncountable : aleph0 < kappa)
    (e : Below kappa → Below kappa) (he : Function.Injective e)
    (hlt : ∀ a, a < e a) :
    ¬ IsStationaryBelow kappa (Set.range e) := by
  classical
  let inverse : Below kappa → Below kappa := fun b ↦
    if hb : b ∈ Set.range e then Classical.choose hb else b
  have hinverse (a : Below kappa) : inverse (e a) = a := by
    have hrange : e a ∈ Set.range e := ⟨a, rfl⟩
    simp only [inverse, dif_pos hrange]
    exact he (Classical.choose_spec hrange)
  have hregressive : IsRegressiveOn (Set.range e) inverse := by
    rintro _ ⟨a, rfl⟩
    rw [hinverse]
    exact hlt a
  have hinjective : Set.InjOn inverse (Set.range e) := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
    rw [hinverse, hinverse] at hab
    exact congrArg e hab
  exact not_isStationaryBelow_of_injOn_regressive
    huncountable hregular hregressive hinjective

/-- Consequently, postcomposing any source chronology with a pointwise-upward
injective reindexing cannot have stationary range. -/
theorem comp_range_not_stationary_of_injective_lt
    {kappa : Cardinal.{u}} (hregular : kappa.IsRegular)
    (huncountable : aleph0 < kappa)
    {X : Type v} (f : X → Below kappa)
    (e : Below kappa → Below kappa) (he : Function.Injective e)
    (hlt : ∀ a, a < e a) :
    ¬ IsStationaryBelow kappa (Set.range (e ∘ f)) := by
  intro hstationary
  have hrange : Set.range (e ∘ f) ⊆ Set.range e := by
    rintro _ ⟨x, rfl⟩
    exact ⟨f x, rfl⟩
  exact range_not_stationary_of_injective_lt hregular huncountable e he hlt
    (hstationary.mono hrange)

end Stationary

namespace DWeb.KappaLadder

open Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- The literal successor-stage repair has nonstationary range. -/
theorem successorStage_range_not_stationary
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal) :
    ¬ Stationary.IsStationaryBelow kappa
      (Set.range (L.successorStage hlegal)) := by
  apply Stationary.range_not_stationary_of_injective_lt
      hlegal.regular hlegal.uncountable
  · intro a b hab
    apply Subtype.ext
    have hval := congrArg Subtype.val hab
    simp only [L.successorStage_val hlegal] at hval
    have hpred := congrArg Ordinal.pred hval
    simpa only [Ordinal.pred_add_one] using hpred
  · intro a
    change a.1 < a.1 + 1
    rw [← Order.succ_eq_add_one]
    exact Order.lt_succ a.1

/-- In particular, postcomposing the concrete stationary source-stage map
with `successorStage` destroys the stationary-range conclusion of Assertion
8.12. -/
theorem successorReindexedAuxiliarySourceRange_not_stationary
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance) :
    ¬ Stationary.IsStationaryBelow kappa
      (Set.range
        (L.successorStage hL.legal ∘ L.auxiliarySourceIndex hL.legal)) := by
  apply Stationary.comp_range_not_stationary_of_injective_lt
      hL.legal.regular hL.legal.uncountable
  · intro a b hab
    apply Subtype.ext
    have hval := congrArg Subtype.val hab
    simp only [L.successorStage_val hL.legal] at hval
    have hpred := congrArg Ordinal.pred hval
    simpa only [Ordinal.pred_add_one] using hpred
  · intro a
    change a.1 < a.1 + 1
    rw [← Order.succ_eq_add_one]
    exact Order.lt_succ a.1

end DWeb.KappaLadder
end Erdos599
