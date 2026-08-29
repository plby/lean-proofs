/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedMarkerStrictRoof
import ErdosProblems.Erdos599.LadderPersistence

/-!
# Literal persistence in the unroofed-marker ladder

The pre-marker arrow fixes every old inessential component. Strict-roof
growth preserves its inessentiality after singleton insertion. The generic
limit argument follows the actual eventually constant path thread; it does
not replace the threadwise limit by a union of the stage families.
-/

noncomputable section

namespace Erdos599.DWeb.KappaLadder

open Set Cardinal Order Ladder

universe u

variable {V : Type u} {G : DWeb V} {kappa : Cardinal.{u}}

/-- Successor persistence extends through genuine limit stages when strict
roofs are monotone. This statement is independent of the marker rule. -/
theorem inessential_mono_of_geometry
    {L : G.KappaLadder kappa} (hgeometry : CanonicalLadderGeometry L)
    (hstep : L.CurrentInessentialPersists)
    (hstrict : ∀ {a b : ExtendedStage kappa}, a ≤ b →
      G.strictRoof (G.terminalFrontier (L.accumulated a)) ⊆
        G.strictRoof (G.terminalFrontier (L.accumulated b)))
    {a b : ExtendedStage kappa} (hab : a ≤ b) :
    G.inessentialPaths (L.accumulated a) ⊆
      G.inessentialPaths (L.accumulated b) := by
  have hmain : ∀ (o : Ordinal.{u}) (ho : o ≤ kappa.ord)
      (c : Ordinal.{u}) (hc : c ≤ o),
      G.inessentialPaths (L.accumulated ⟨c, hc.trans ho⟩) ⊆
        G.inessentialPaths (L.accumulated ⟨o, ho⟩) := by
    intro o
    induction o using Ordinal.limitRecOn with
    | zero =>
        intro ho c hc
        have hc0 : c = 0 := le_antisymm hc bot_le
        subst c
        exact Set.Subset.rfl
    | add_one o ih =>
        intro ho c hc
        rcases hc.lt_or_eq with hc | rfl
        · have hco : c ≤ o := (Order.lt_add_one_iff).mp hc
          have hoo : o ≤ o + 1 := by
            rw [← Order.succ_eq_add_one]
            exact le_succ o
          let s : Stage kappa := ⟨o, (Order.add_one_le_iff).mp ho⟩
          exact (ih (hoo.trans ho) c hco).trans (hstep s)
        · exact Set.Subset.rfl
    | limit o hoLimit ih =>
        intro ho c hc p hp
        rcases hc.lt_or_eq with hc | rfl
        · obtain ⟨C, hstage, hfinal⟩ := hgeometry.limitStages ⟨o, ho⟩ hoLimit
          let : Nonempty (Set.Iio o) := hoLimit.nonempty_Iio.to_subtype
          let ci : Set.Iio o := ⟨c, hc⟩
          have hpCi : p ∈ G.inessentialPaths (C.stage ci) := by
            rw [hstage ci]
            exact hp
          have hpTail : ∀ d, ci ≤ d → p ∈ G.inessentialPaths (C.stage d) := by
            intro d hcd
            rw [hstage d]
            exact ih d.1 d.2 (d.2.le.trans ho) c hcd hp
          have hstrictLimit :
              G.strictRoof (G.terminalFrontier (C.stage ci)) ⊆
                G.strictRoof (G.terminalFrontier (C.limitPaths G)) := by
            rw [hstage ci, ← hfinal]
            exact hstrict (a := ⟨c, hc.le.trans ho⟩) (b := ⟨o, ho⟩) hc.le
          rw [hfinal]
          exact C.mem_inessentialPaths_limitPaths_of_tail ci hpCi hpTail hstrictLimit
        · exact hp
  exact hmain b.1 b.2 a.1 hab

end Erdos599.DWeb.KappaLadder

namespace Erdos599.DWeb.UnroofedMarker

open Set Cardinal Order Ladder KappaLadder

universe u

variable {V : Type u}

/-- The canonical rung, independently of the marker rule, leaves each
inessential old member literally fixed in the pre-marker arrow. -/
theorem mem_preMarker_of_mem_inessentialPaths (G : DWeb V)
    (s : G.LadderAccumulationState) {p : G.DPath}
    (hp : p ∈ G.inessentialPaths s.1) : p ∈ preMarker G s := by
  rcases p with p | r
  · have hfinish := G.terminal_mem_strictRoof_of_mem_inessentialPaths hp rfl
    exact ⟨⟨.inl p, hp.1⟩,
      G.arrowPath_eq_of_terminal_mem_strictRoof_liftedRung s p hp.1 hfinish⟩
  · exact ⟨⟨.inr r, hp.1⟩,
      G.arrowPath_ray s.1 (G.liftedLadderRungOfState s) r hp.1⟩

theorem ladder_currentInessentialPersists (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source) :
    (ladder G kappa preferred).CurrentInessentialPersists := by
  intro a p hp
  have hpNext : p ∈ (ladder G kappa preferred).successorWarp a := by
    rw [ladder_successor_eq_arrow_union_marker]
    exact Or.inl (mem_preMarker_of_mem_inessentialPaths G
      (state G (extendLadderPreference kappa preferred) a.1) hp)
  rcases p with p | r
  · apply G.mem_inessentialPaths_of_terminal_mem_strictRoof hpNext rfl
    exact ladder_strictRoof_successor G kappa preferred hNoEnter a
      (G.terminal_mem_strictRoof_of_mem_inessentialPaths hp rfl)
  · exact G.ray_mem_inessentialPaths hpNext

/-- The same inessential path occurs at every later extended stage. -/
theorem ladder_inessential_mono (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    {a b : ExtendedStage kappa} (hab : a ≤ b) :
    G.inessentialPaths ((ladder G kappa preferred).accumulated a) ⊆
      G.inessentialPaths ((ladder G kappa preferred).accumulated b) := by
  apply inessential_mono_of_geometry (ladder_geometry G kappa preferred hNoEnter)
    (ladder_currentInessentialPersists G kappa preferred hNoEnter)
    (fun h ↦ ladder_strictRoof_mono G kappa preferred hNoEnter h) hab

/-- Exact successor-indexed record persistence, including the final warp. -/
theorem ladder_recordedPathsPersist (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source) :
    (ladder G kappa preferred).RecordedPathsPersist := by
  let L := ladder G kappa preferred
  intro a p hp b hab
  have hpNext : p ∈ G.inessentialPaths (L.successorWarp a) :=
    (L.bookkeeping.chosen_mem_available (ladder_validBookkeeping G kappa preferred) hp).1
  exact ladder_inessential_mono G kappa preferred hNoEnter hab hpNext

#print axioms ladder_inessential_mono
#print axioms ladder_recordedPathsPersist

end Erdos599.DWeb.UnroofedMarker
