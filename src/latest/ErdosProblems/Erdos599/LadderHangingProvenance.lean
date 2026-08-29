/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LadderRoofRecursion

/-!
# Initial-vertex provenance for hanging ladder records

This file isolates the last purely formal step in the hanging-record
argument.  If every accumulated component starts either at an original
source or at a marker already inserted by the time of that accumulation,
then a component chosen from the current accumulated family has the same
provenance.  Since the marker at stage `a` is inserted only into
`Y_(a+1)`, every marker origin of a component of `Y_a` is strictly earlier.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

universe u

variable {V : Type u} {G : DWeb V} {kappa : Cardinal.{u}}

/-- Initial-vertex provenance at every accumulated stage.  A marker born
at stage `b` may occur from `b + 1` onward, encoded by
`Stage.succExtended b ≤ a`. -/
def HasAccumulatedInitialProvenance (L : G.KappaLadder kappa) : Prop :=
  ∀ (a : Ladder.ExtendedStage kappa) (p : G.DPath),
    p ∈ L.accumulated a →
      p.initial ∈ G.source ∨
        ∃ b : Ladder.Stage kappa,
          Ladder.Stage.succExtended b ≤ a ∧
            L.marker b = some p.initial

/-- Source-faithful stage convention for the recorded obstruction: the
path named at `a` is already inessential in `Y_a`, before the marker
`y_a` is inserted. -/
def ChosenPathsAreCurrent (L : G.KappaLadder kappa) : Prop :=
  ∀ (a : Ladder.Stage kappa) (p : G.DPath), L.chosen a = some p →
    p ∈ G.inessentialPaths (L.warpAt a)

/-- The exact same-stage exclusion needed to turn successor-normalized
initial provenance into strict earlier-marker provenance.  This predicate is
strictly weaker than `ChosenPathsAreCurrent`: it permits genuinely new arrow
records at a successor, but rules out recording a component whose initial
vertex is the marker inserted at that very stage. -/
def ChosenPathsAvoidCurrentMarker (L : G.KappaLadder kappa) : Prop :=
  ∀ (a : Ladder.Stage kappa) (p : G.DPath), L.chosen a = some p →
    L.marker a ≠ some p.initial

/-- Under the source's current-stage convention, accumulated provenance
immediately gives strict earlier-marker provenance.  No claim about the
essentiality of the newly inserted marker is needed. -/
theorem hasHangingProvenance_of_accumulatedInitialProvenance_of_current
    {L : G.KappaLadder kappa}
    (hprovenance : L.HasAccumulatedInitialProvenance)
    (hcurrent : L.ChosenPathsAreCurrent) :
    L.HasHangingProvenance := by
  intro a ha p hp
  have hpCurrent := hcurrent a p hp
  rcases hprovenance (Ladder.Stage.toExtended a) p hpCurrent.1 with
      hpSource | ⟨b, hba, hb⟩
  · exact (ha.2 ⟨p, hp, hpSource⟩).elim
  · refine ⟨b, ?_, hb⟩
    change b.1 + 1 ≤ a.1 at hba
    change b.1 < a.1
    exact (Order.add_one_le_iff).1 hba

/-- For successor-normalized bookkeeping, accumulated provenance gives a
marker stage `b ≤ a`.  Excluding the marker born at `a` is exactly what is
needed to strengthen this to `b < a`; no current-stage membership hypothesis
is otherwise required. -/
theorem hasHangingProvenance_of_accumulatedInitialProvenance_of_avoidsCurrentMarker
    {L : G.KappaLadder kappa}
    (hprovenance : L.HasAccumulatedInitialProvenance)
    (hvalid : L.HasValidBookkeeping)
    (havoid : L.ChosenPathsAvoidCurrentMarker) :
    L.HasHangingProvenance := by
  intro a ha p hp
  have hpNext : p ∈ G.inessentialPaths (L.successorWarp a) :=
    (L.bookkeeping.chosen_mem_available hvalid hp).1
  rcases hprovenance (Ladder.Stage.succExtended a) p hpNext.1 with
      hpSource | ⟨b, hba, hb⟩
  · exact (ha.2 ⟨p, hp, hpSource⟩).elim
  · refine ⟨b, ?_, hb⟩
    have hble : b.1 ≤ a.1 := by
      change b.1 + 1 ≤ a.1 + 1 at hba
      rw [← Order.succ_eq_add_one, ← Order.succ_eq_add_one] at hba
      exact Order.succ_le_succ_iff.mp hba
    exact hble.lt_of_ne (by
      intro hbaEq
      apply havoid a p hp
      simpa [Subtype.ext hbaEq] using hb)

/-- Every component of the canonical accumulated family starts either in
the original source or at a marker whose successor stage is no later than
the current accumulated stage. -/
theorem canonicalLadder_hasAccumulatedInitialProvenance
    (preferred : Ladder.Stage kappa → Option V)
    (hNoEnter : G.NoEdgeEnters G.source) :
    (canonicalLadder G kappa preferred).HasAccumulatedInitialProvenance := by
  let L := canonicalLadder G kappa preferred
  have hgeometry : CanonicalLadderGeometry L :=
    canonicalLadder_geometry preferred hNoEnter
  have hprovenance : ∀ (o : Ordinal.{u}) (ho : o ≤ kappa.ord)
      (p : G.DPath), p ∈ L.accumulated ⟨o, ho⟩ →
        p.initial ∈ G.source ∨
          ∃ b : Ladder.Stage kappa,
            Ladder.Stage.succExtended b ≤ ⟨o, ho⟩ ∧
              L.marker b = some p.initial := by
    intro o
    induction o using Ordinal.limitRecOn with
    | zero =>
        intro ho p hp
        have hzero : (⟨0, ho⟩ : Ladder.ExtendedStage kappa) =
            Ladder.zeroStage kappa := Subtype.ext rfl
        have hp' : p ∈ G.trivialWave := by
          change p ∈ G.canonicalLadderAccumulated kappa preferred ⟨0, ho⟩ at hp
          rw [hzero] at hp
          simpa [canonicalLadderAccumulated, canonicalLadderState] using hp
        exact Or.inl (G.initialSet_trivialWave ▸ ⟨p, hp', rfl⟩)
    | add_one o ih =>
        intro ho p hp
        have hoStage : o < kappa.ord := (Order.add_one_le_iff).1 ho
        let a : Ladder.Stage kappa := ⟨o, hoStage⟩
        let s := G.canonicalLadderState kappa preferred
          (Ladder.Stage.toExtended a)
        have hsucc : (⟨o + 1, ho⟩ : Ladder.ExtendedStage kappa) =
            Ladder.Stage.succExtended a := Subtype.ext rfl
        have hpStep : p ∈
            (G.ladderSuccessorState
              (extendLadderPreference kappa preferred) o s).1 := by
          change p ∈ G.canonicalLadderAccumulated kappa preferred ⟨o + 1, ho⟩ at hp
          rw [hsucc] at hp
          simpa [canonicalLadderAccumulated, canonicalLadderState,
            ladderAccumulatedState_succ, a, s] using hp
        by_cases hactive : s.2 = true
        · rw [ladderSuccessorState, dif_pos hactive] at hpStep
          have hpref : extendLadderPreference kappa preferred o =
              preferred a := by
            simpa [a] using extendLadderPreference_stage
              preferred a
          rw [hpref] at hpStep
          rcases hpStep with hpArrow | hpMarker
          · have hpInitial :
                p.initial ∈ G.initialSet s.1 := by
              rw [G.initialSet_eq_of_forwardExtension
                (G.forwardExtension_arrow s.1
                  (G.liftedLadderRungOfState s))]
              exact ⟨p, hpArrow, rfl⟩
            obtain ⟨q, hq, hqp⟩ := hpInitial
            have hoo : o ≤ o + 1 := by
              rw [← Order.succ_eq_add_one]
              exact le_succ o
            have hcurrent : Ladder.Stage.toExtended a =
                (⟨o, le_trans hoo ho⟩ : Ladder.ExtendedStage kappa) :=
              Subtype.ext rfl
            have hqProvenance := ih (le_trans hoo ho) q (by
              change q ∈ G.canonicalLadderAccumulated kappa preferred
                (Ladder.Stage.toExtended a) at hq
              rw [hcurrent] at hq
              exact hq)
            rcases hqProvenance with hqSource | ⟨b, hbStage, hbMarker⟩
            · exact Or.inl (hqp ▸ hqSource)
            · exact Or.inr ⟨b, hbStage.trans (by
                change o ≤ o + 1
                exact hoo), by simpa [hqp] using hbMarker⟩
          · cases hmarker : G.ladderMarkerOfState
                (preferred a) s with
            | none =>
                simp [ladderMarkerPathSetOfState, hmarker,
                  ] at hpMarker
            | some y =>
                have hpEq : p = G.trivialPath y := by
                  simpa [ladderMarkerPathSetOfState, hmarker,
                    ] using hpMarker
                subst p
                exact Or.inr ⟨a, le_rfl, by
                  change G.ladderMarkerOfState (preferred a) s = some y
                  exact hmarker⟩
        · rw [ladderSuccessorState, dif_neg hactive] at hpStep
          have hoo : o ≤ o + 1 := by
            rw [← Order.succ_eq_add_one]
            exact le_succ o
          have hcurrent : Ladder.Stage.toExtended a =
              (⟨o, le_trans hoo ho⟩ : Ladder.ExtendedStage kappa) :=
            Subtype.ext rfl
          have hpProvenance := ih (le_trans hoo ho) p (by
            change p ∈ G.canonicalLadderAccumulated kappa preferred
              (Ladder.Stage.toExtended a) at hpStep
            rw [hcurrent] at hpStep
            exact hpStep)
          rcases hpProvenance with hpSource | ⟨b, hbStage, hbMarker⟩
          · exact Or.inl hpSource
          · exact Or.inr ⟨b, hbStage.trans (by
              change o ≤ o + 1
              exact hoo), hbMarker⟩
    | limit o hoLimit ih =>
        intro ho p hp
        let a : Ladder.ExtendedStage kappa := ⟨o, ho⟩
        obtain ⟨C, hstage, hlimit⟩ :=
          hgeometry.limitStages a hoLimit
        have hpInitial : p.initial ∈ C.initialUnion := by
          rw [← C.initialSet_limitPaths G, ← hlimit]
          exact ⟨p, hp, rfl⟩
        obtain ⟨b, q, hq, hqp⟩ := Set.mem_iUnion.1 hpInitial
        have hbo : b.1 ≤ kappa.ord := b.2.le.trans ho
        have hqAccumulated : q ∈ L.accumulated ⟨b.1, hbo⟩ := by
          rw [← hstage b]
          exact hq
        rcases ih b.1 b.2 hbo q hqAccumulated with
            hqSource | ⟨c, hcStage, hcMarker⟩
        · exact Or.inl (hqp ▸ hqSource)
        · exact Or.inr ⟨c, hcStage.trans b.2.le, by
            simpa [hqp] using hcMarker⟩
  intro a p hp
  exact hprovenance a.1 a.2 p hp

/-- The successor-normalized bookkeeping gives a non-strict marker-origin
bound without any further hypothesis.  The possible equality is exactly the
same-stage marker branch: records are selected from `IE (Y_(a+1))`, while the
marker born at `a` is already present in `Y_(a+1)`. -/
theorem canonicalLadder_hasHangingProvenance_le
    (preferred : Ladder.Stage kappa → Option V)
    (hNoEnter : G.NoEdgeEnters G.source) :
    ∀ (a : Ladder.Stage kappa),
      a ∈ (canonicalLadder G kappa preferred).phiHanging →
      ∀ (p : G.DPath),
        (canonicalLadder G kappa preferred).chosen a = some p →
        ∃ b : Ladder.Stage kappa,
          b ≤ a ∧
            (canonicalLadder G kappa preferred).marker b = some p.initial := by
  let L := canonicalLadder G kappa preferred
  have hvalid : L.HasValidBookkeeping :=
    (G.canonicalLadderCore kappa preferred)
      |>.withValidBookkeeping_hasValidBookkeeping
  have hprovenance : L.HasAccumulatedInitialProvenance :=
    canonicalLadder_hasAccumulatedInitialProvenance preferred hNoEnter
  intro a ha p hp
  have hpNext : p ∈ G.inessentialPaths (L.successorWarp a) :=
    (L.bookkeeping.chosen_mem_available hvalid hp).1
  rcases hprovenance (Ladder.Stage.succExtended a) p hpNext.1 with
      hpSource | ⟨b, hba, hb⟩
  · exact (ha.2 ⟨p, hp, hpSource⟩).elim
  · refine ⟨b, ?_, hb⟩
    change b.1 + 1 ≤ a.1 + 1 at hba
    change b.1 ≤ a.1
    rw [← Order.succ_eq_add_one, ← Order.succ_eq_add_one] at hba
    exact (Order.succ_le_succ_iff).1 hba

/-- The precise remaining implication from successor-normalized provenance
to the strict regressive provenance required by legality.  It suffices to
show that the bookkeeping never selects a path whose initial vertex is the
marker inserted at that very stage. -/
theorem hasHangingProvenance_of_le_of_avoids_currentMarker
    {L : G.KappaLadder kappa}
    (hle : ∀ (a : Ladder.Stage kappa), a ∈ L.phiHanging →
      ∀ (p : G.DPath), L.chosen a = some p →
        ∃ b : Ladder.Stage kappa,
          b ≤ a ∧ L.marker b = some p.initial)
    (havoid : ∀ (a : Ladder.Stage kappa) (p : G.DPath),
      L.chosen a = some p → L.marker a ≠ some p.initial) :
    L.HasHangingProvenance := by
  intro a ha p hp
  obtain ⟨b, hba, hb⟩ := hle a ha p hp
  refine ⟨b, ?_, hb⟩
  rcases hba.lt_or_eq with hba | hba
  · exact hba
  · subst b
    exact (havoid a p hp hb).elim

end KappaLadder
end DWeb
end Erdos599
