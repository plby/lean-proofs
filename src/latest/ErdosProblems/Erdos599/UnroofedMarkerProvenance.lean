/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedMarkerArrows
import ErdosProblems.Erdos599.LadderHangingProvenance

/-!
# Initial and hanging-record provenance for the unroofed ladder

Only the actual initial sets, singleton insertions and threadwise limit
law enter the provenance induction. A selected path may genuinely appear
in the successor arrow. The strict earlier-marker bound uses the proved
essentiality of the current marker, not a false current-stage hypothesis.
-/

noncomputable section

namespace Erdos599.DWeb.KappaLadder

open Set Cardinal Order Ladder

universe u

variable {V : Type u} {G : DWeb V} {kappa : Cardinal.{u}}

/-- The initial-set form of the successor rule suffices for provenance. -/
theorem hasAccumulatedInitialProvenance_of_initialSets
    {L : G.KappaLadder kappa} (hzero : L.HasInitialStage)
    (hlimit : L.HasLimitStages)
    (hstep : ∀ a : Stage kappa,
      G.initialSet (L.successorWarp a) ⊆
        G.initialSet (L.warpAt a) ∪ {x | L.marker a = some x}) :
    L.HasAccumulatedInitialProvenance := by
  have hmain : ∀ (o : Ordinal.{u}) (ho : o ≤ kappa.ord) (p : G.DPath),
      p ∈ L.accumulated ⟨o, ho⟩ →
        p.initial ∈ G.source ∨
          ∃ b : Stage kappa, Stage.succExtended b ≤ ⟨o, ho⟩ ∧
            L.marker b = some p.initial := by
    intro o
    induction o using Ordinal.limitRecOn with
    | zero =>
        intro ho p hp
        have hpZero : p ∈ L.accumulated (zeroStage kappa) := hp
        rw [hzero] at hpZero
        exact Or.inl (G.initialSet_trivialWave ▸ ⟨p, hpZero, rfl⟩)
    | add_one o ih =>
        intro ho p hp
        have hoo : o ≤ o + 1 := by
          rw [← Order.succ_eq_add_one]
          exact le_succ o
        let a : Stage kappa := ⟨o, (Order.add_one_le_iff).mp ho⟩
        have hpNext : p ∈ L.successorWarp a := hp
        rcases hstep a ⟨p, hpNext, rfl⟩ with hpOld | hpMarker
        · obtain ⟨q, hq, hqp⟩ := hpOld
          rcases ih (hoo.trans ho) q hq with hsource | ⟨b, hb, hmarker⟩
          · exact Or.inl (hqp ▸ hsource)
          · exact Or.inr ⟨b, hb.trans hoo, by simpa only [hqp] using hmarker⟩
        · exact Or.inr ⟨a, le_rfl, hpMarker⟩
    | limit o hoLimit ih =>
        intro ho p hp
        let a : ExtendedStage kappa := ⟨o, ho⟩
        obtain ⟨C, hstage, hfinal⟩ := hlimit a hoLimit
        have hpInitial : p.initial ∈ C.initialUnion := by
          rw [← C.initialSet_limitPaths G, ← hfinal]
          exact ⟨p, hp, rfl⟩
        obtain ⟨b, q, hq, hqp⟩ := Set.mem_iUnion.mp hpInitial
        have hqOld : q ∈ L.accumulated ⟨b.1, b.2.le.trans ho⟩ := by
          rw [← hstage b]
          exact hq
        rcases ih b.1 b.2 (b.2.le.trans ho) q hqOld with
            hsource | ⟨c, hc, hmarker⟩
        · exact Or.inl (hqp ▸ hsource)
        · exact Or.inr ⟨c, hc.trans b.2.le, by simpa only [hqp] using hmarker⟩
  intro a p hp
  exact hmain a.1 a.2 p hp

end Erdos599.DWeb.KappaLadder

namespace Erdos599.DWeb.UnroofedMarker

open Set Cardinal Order Ladder KappaLadder

universe u

variable {V : Type u}

theorem ladder_hasAccumulatedInitialProvenance (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source) :
    (ladder G kappa preferred).HasAccumulatedInitialProvenance := by
  let L := ladder G kappa preferred
  apply hasAccumulatedInitialProvenance_of_initialSets
    (ladder_hasInitialStage G kappa preferred)
    (ladder_geometry G kappa preferred hNoEnter).limitStages
  intro a
  rw [ladder_successor_eq_arrow_union_marker, G.initialSet_union,
    ← G.initialSet_eq_of_forwardExtension
      (G.forwardExtension_arrow (L.warpAt a) (L.liftedRung a))]
  rintro x (hx | ⟨p, hp, hpx⟩)
  · exact Or.inl hx
  · right
    change L.marker a = some x
    change p ∈ L.markerPathSet a at hp
    cases hm : L.marker a with
    | none => simp [markerPathSet, hm] at hp
    | some y =>
        have hpEq : p = G.trivialPath y := by simpa [markerPathSet, hm] using hp
        subst p
        have hyx : y = x := hpx
        exact congrArg some hyx

/-- Strict marker provenance for every hanging selected component. -/
theorem ladder_hasHangingProvenance (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source) :
    (ladder G kappa preferred).HasHangingProvenance := by
  apply hasHangingProvenance_of_accumulatedInitialProvenance_of_avoidsCurrentMarker
    (ladder_hasAccumulatedInitialProvenance G kappa preferred hNoEnter)
    (ladder_validBookkeeping G kappa preferred)
  intro a p hp hm
  exact ladder_chosen_avoids_current_marker G kappa preferred hNoEnter hp hm
    p.initial_mem_support

#print axioms ladder_hasAccumulatedInitialProvenance
#print axioms ladder_hasHangingProvenance

end Erdos599.DWeb.UnroofedMarker
