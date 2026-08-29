/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedMarkerArrows
import ErdosProblems.Erdos599.LadderStrictChronology

/-!
# Strict roofs through the unroofed-marker recursion

The shared limit lemma propagates strict roofs through actual threadwise
limits. The successor input is the maximal-rung arrow lemma followed by
ordinary enlargement of the terminal set. Marker exhaustion is irrelevant.
-/

noncomputable section

namespace Erdos599.DWeb.KappaLadder

open Set Cardinal Order Ladder

universe u

variable {V : Type u} {G : DWeb V} {kappa : Cardinal.{u}}

/-- Local strict-roof growth and genuine limit geometry imply global
strict-roof monotonicity, for any marker rule. -/
theorem strictRoof_mono_of_geometry
    {L : G.KappaLadder kappa} (hgeometry : CanonicalLadderGeometry L)
    (hstep : ∀ a : Stage kappa,
      G.strictRoof (G.terminalFrontier (L.warpAt a)) ⊆
        G.strictRoof (G.terminalFrontier (L.successorWarp a)))
    {a b : ExtendedStage kappa} (hab : a ≤ b) :
    G.strictRoof (G.terminalFrontier (L.accumulated a)) ⊆
      G.strictRoof (G.terminalFrontier (L.accumulated b)) := by
  have hmain : ∀ (o : Ordinal.{u}) (ho : o ≤ kappa.ord)
      (c : Ordinal.{u}) (hc : c ≤ o),
      G.strictRoof (G.terminalFrontier (L.accumulated ⟨c, hc.trans ho⟩)) ⊆
        G.strictRoof (G.terminalFrontier (L.accumulated ⟨o, ho⟩)) := by
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
        intro ho c hc
        rcases hc.lt_or_eq with hc | rfl
        · obtain ⟨C, hstage, hfinal⟩ := hgeometry.limitStages ⟨o, ho⟩ hoLimit
          let : Nonempty (Set.Iio o) := hoLimit.nonempty_Iio.to_subtype
          let ci : Set.Iio o := ⟨c, hc⟩
          have hself : ∀ i, G.vertexSet (C.stage i) ⊆
              G.roof (G.terminalFrontier (C.stage i)) := by
            intro i
            rw [hstage i]
            exact hgeometry.selfRoofing _
          have hstrict : ∀ {i j : Set.Iio o}, i ≤ j →
              G.strictRoof (G.terminalFrontier (C.stage i)) ⊆
                G.strictRoof (G.terminalFrontier (C.stage j)) := by
            intro i j hij
            rw [hstage i, hstage j]
            exact ih j.1 j.2 (j.2.le.trans ho) i.1 hij
          have h := C.strictRoof_terminalFrontier_subset_limitPaths hself @hstrict ci
          rwa [hstage ci, ← hfinal] at h
        · exact Set.Subset.rfl
  exact hmain b.1 b.2 a.1 hab

end Erdos599.DWeb.KappaLadder

namespace Erdos599.DWeb.UnroofedMarker

open Set Cardinal Order Ladder KappaLadder

universe u

variable {V : Type u}

theorem ladder_strictRoof_successor (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    (a : Stage kappa) :
    G.strictRoof (G.terminalFrontier ((ladder G kappa preferred).warpAt a)) ⊆
      G.strictRoof (G.terminalFrontier ((ladder G kappa preferred).successorWarp a)) := by
  rw [ladder_successor_eq_arrow_union_marker, G.terminalFrontier_union]
  have hinv := state_invariant G (extendLadderPreference kappa preferred) hNoEnter a.1
  exact (G.strictRoof_terminalFrontier_subset_canonicalArrow hNoEnter
    (state G (extendLadderPreference kappa preferred) a.1)
    hinv.warp hinv.selfRoof hinv.sourceRoof).trans
    (G.strictRoof_subset_strictRoof_union_left _ _)

theorem ladder_strictRoof_mono (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    {a b : ExtendedStage kappa} (hab : a ≤ b) :
    G.strictRoof (G.terminalFrontier ((ladder G kappa preferred).accumulated a)) ⊆
      G.strictRoof (G.terminalFrontier ((ladder G kappa preferred).accumulated b)) :=
  strictRoof_mono_of_geometry (ladder_geometry G kappa preferred hNoEnter)
    (ladder_strictRoof_successor G kappa preferred hNoEnter) hab

theorem ladder_hasStrictFrontierChronology (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source) :
    (ladder G kappa preferred).HasStrictFrontierChronology := by
  apply (ladder G kappa preferred).hasStrictFrontierChronology_of_strictRoof_mono
    (ladder_geometry G kappa preferred hNoEnter).roofsSourceAtStages
  intro a b hab
  exact ladder_strictRoof_mono G kappa preferred hNoEnter
    (a := Stage.toExtended a) (b := Stage.toExtended b) hab.le

#print axioms ladder_strictRoof_mono
#print axioms ladder_hasStrictFrontierChronology

end Erdos599.DWeb.UnroofedMarker
