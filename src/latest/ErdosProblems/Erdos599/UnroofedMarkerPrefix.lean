/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedMarkerLadder

/-!
# Prefix causality of the unroofed-marker recursion and its records

Accumulated states use only strict-prior preferences. Markers and successor
warps also use the current preference. The already proved bookkeeping
prefix theorem transfers successor-family agreement to chosen records.
This is the causal-row bridge for the new marker rule, not an identification
with the historical canonical ladder.
-/

namespace Erdos599.DWeb.UnroofedMarker

open Set Cardinal Order Ladder KappaLadder

universe u

variable {V : Type u} (G : DWeb V)

theorem state_congr_prefix (p q : Ordinal.{u} → Option V) :
    ∀ a : Ordinal.{u}, (∀ b, b < a → p b = q b) → state G p a = state G q a := by
  intro a
  induction a using Ordinal.limitRecOn with
  | zero =>
      intro _h
      simp only [state, DWeb.ladderAccumulatedStateAux, Ordinal.limitRecOn_zero]
  | add_one a ih =>
      intro h
      rw [state_succ, state_succ, ih (fun b hb ↦ h b (hb.trans (lt_add_one a)))]
      simp only [step, h a (lt_add_one a)]
  | limit a ha ih =>
      intro h
      change G.ladderAccumulatedStateAux (step G p) a =
        G.ladderAccumulatedStateAux (step G q) a
      rw [DWeb.ladderAccumulatedStateAux, Ordinal.limitRecOn_limit _ _ _ _ ha,
        DWeb.ladderAccumulatedStateAux, Ordinal.limitRecOn_limit _ _ _ _ ha]
      apply congrArg (G.ladderLimitState a ha)
      funext b hb
      exact ih b hb (fun c hc ↦ h c (hc.trans hb))

variable (kappa : Cardinal.{u}) (p q : Stage kappa → Option V)

theorem extendedState_eq_of_forall_lt (a : ExtendedStage kappa)
    (h : ∀ b : Stage kappa, b.1 < a.1 → p b = q b) :
    state G (extendLadderPreference kappa p) a.1 =
      state G (extendLadderPreference kappa q) a.1 := by
  apply state_congr_prefix
  intro b hb
  have hbk : b < kappa.ord := hb.trans_le a.2
  simpa only [extendLadderPreference, dif_pos hbk] using h ⟨b, hbk⟩ hb

theorem accumulated_eq_of_forall_lt (a : ExtendedStage kappa)
    (h : ∀ b : Stage kappa, b.1 < a.1 → p b = q b) :
    (ladder G kappa p).accumulated a = (ladder G kappa q).accumulated a :=
  congrArg Prod.fst (extendedState_eq_of_forall_lt G kappa p q a h)

theorem warpAt_eq_of_forall_lt (a : Stage kappa)
    (h : ∀ b, b < a → p b = q b) :
    (ladder G kappa p).warpAt a = (ladder G kappa q).warpAt a :=
  accumulated_eq_of_forall_lt G kappa p q (Stage.toExtended a) h

theorem stageWeb_eq_of_forall_lt (a : Stage kappa)
    (h : ∀ b, b < a → p b = q b) :
    (ladder G kappa p).stageWeb a = (ladder G kappa q).stageWeb a := by
  unfold KappaLadder.stageWeb
  rw [warpAt_eq_of_forall_lt G kappa p q a h]

theorem frontier_eq_of_forall_lt (a : Stage kappa)
    (h : ∀ b, b < a → p b = q b) :
    (ladder G kappa p).frontier a = (ladder G kappa q).frontier a :=
  congrArg DWeb.source (stageWeb_eq_of_forall_lt G kappa p q a h)

theorem successorWarp_eq_of_forall_le (a : Stage kappa)
    (h : ∀ b, b ≤ a → p b = q b) :
    (ladder G kappa p).successorWarp a = (ladder G kappa q).successorWarp a := by
  apply accumulated_eq_of_forall_lt G kappa p q (Stage.succExtended a)
  intro b hb
  have hle : b.1 ≤ a.1 := Order.lt_add_one_iff.mp (show b.1 < a.1 + 1 from hb)
  exact h b hle

theorem marker_eq_of_forall_le (a : Stage kappa)
    (h : ∀ b, b ≤ a → p b = q b) :
    (ladder G kappa p).marker a = (ladder G kappa q).marker a := by
  change selectMarker G (extendLadderPreference kappa p a.1)
      (state G (extendLadderPreference kappa p) a.1) =
    selectMarker G (extendLadderPreference kappa q a.1)
      (state G (extendLadderPreference kappa q) a.1)
  have hstate : state G (extendLadderPreference kappa p) a.1 =
      state G (extendLadderPreference kappa q) a.1 :=
    extendedState_eq_of_forall_lt G kappa p q (Stage.toExtended a) (fun b hb ↦ h b hb.le)
  rw [hstate]
  simp only [extendLadderPreference, h a le_rfl]

theorem chosen_eq_of_forall_le (a : Stage kappa)
    (h : ∀ b, b ≤ a → p b = q b) :
    (ladder G kappa p).chosen a = (ladder G kappa q).chosen a := by
  apply Ladder.Bookkeeping.ofData_chosen_congr_le
  intro b hb
  exact congrArg G.inessentialPaths
    (successorWarp_eq_of_forall_le G kappa p q b (fun c hc ↦ h c (hc.trans hb)))

theorem recordedBefore_eq_of_forall_lt (a : Stage kappa)
    (h : ∀ b, b < a → p b = q b) :
    (ladder G kappa p).bookkeeping.recordedBefore a =
      (ladder G kappa q).bookkeeping.recordedBefore a := by
  have hchosen : ∀ b, b < a →
      (ladder G kappa p).chosen b = (ladder G kappa q).chosen b := by
    intro b hb
    exact chosen_eq_of_forall_le G kappa p q b (fun c hc ↦ h c (hc.trans_lt hb))
  ext P
  constructor
  · rintro ⟨b, hb, hP⟩
    exact ⟨b, hb, (hchosen b hb).symm.trans hP⟩
  · rintro ⟨b, hb, hP⟩
    exact ⟨b, hb, (hchosen b hb).trans hP⟩

#print axioms state_congr_prefix
#print axioms warpAt_eq_of_forall_lt
#print axioms marker_eq_of_forall_le
#print axioms chosen_eq_of_forall_le
#print axioms recordedBefore_eq_of_forall_lt

end Erdos599.DWeb.UnroofedMarker
