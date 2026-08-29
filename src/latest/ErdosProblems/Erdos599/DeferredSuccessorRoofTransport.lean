/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingChronology
import ErdosProblems.Erdos599.LadderPersistence
import ErdosProblems.Erdos599.LadderStrictChronology

/-!
# Canonical deferred successor-roof transport

This file proves the geometric part of source Lemma 7.17 for the canonical
ladder with deferred current-marker bookkeeping.  The first ingredient is
the no-reentry law below: a canonical successor never introduces a new
vertex in the strict roof of the preceding accumulator.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb

universe u

variable {V : Type u} {G : DWeb V}

/-- A canonical successor introduces no new point in the old strict roof.
The old arrow contributes only old vertices and vertices of the lifted rung;
the latter live in the quotient region.  The optional marker is chosen in
that same quotient region. -/
theorem vertexSet_ladderSuccessorState_inter_strictRoof_subset
    (preferred : Ordinal.{u} → Option V) (o : Ordinal.{u})
    (s : G.LadderAccumulationState) :
    G.vertexSet (G.ladderSuccessorState preferred o s).1 ∩
        G.strictRoof (G.terminalFrontier s.1) ⊆
      G.vertexSet s.1 := by
  classical
  intro x hx
  by_cases hs : s.2 = true
  · rw [ladderSuccessorState, dif_pos hs] at hx
    change x ∈ G.vertexSet
        (G.activeLadderSuccessor (preferred o) s) ∩ _ at hx
    rw [activeLadderSuccessor, G.vertexSet_union] at hx
    rcases hx.1 with hxArrow | hxMarker
    · rcases G.vertexSet_arrow_subset s.1
          (G.liftedLadderRungOfState s) hxArrow with hxOld | hxRung
      · exact hxOld
      · exact False.elim <| Set.disjoint_left.1
          (G.disjoint_vertexSet_liftedLadderRungOfState_strictRoof s)
          hxRung hx.2
    · cases hm : G.ladderMarkerOfState (preferred o) s with
      | none =>
          rcases hxMarker with ⟨p, hp, _⟩
          simp [ladderMarkerPathSetOfState, hm] at hp
      | some y =>
          have hyCandidates : y ∈ G.ladderMarkerCandidatesOfState s :=
            G.ladderMarkerOfState_mem_candidates hm
          have hyNotStrict : y ∉
              G.strictRoof (G.terminalFrontier s.1) := hyCandidates.1.2
          rcases hxMarker with ⟨p, hp, hxp⟩
          have hpEq : p = G.trivialPath y := by
            simpa [ladderMarkerPathSetOfState, hm] using hp
          subst p
          rw [G.support_trivialPath] at hxp
          have hxy : x = y := by simpa using hxp
          exact False.elim (hyNotStrict (hxy ▸ hx.2))
  · rw [ladderSuccessorState, dif_neg hs] at hx
    exact hx.1

/-- Pathwise ladder growth is also monotone on the union of path
supports. -/
theorem vertexSet_mono_of_ladderGrows {U W : Set G.DPath}
    (hUW : G.LadderGrows U W) :
    G.vertexSet U ⊆ G.vertexSet W := by
  rintro x ⟨p, hp, hxp⟩
  obtain ⟨q, hq, hpq⟩ := hUW p hp
  exact ⟨q, hq, G.support_mono_of_extends hpq hxp⟩

namespace KappaLadder

open Ladder

variable {κ : Cardinal.{u}}

/-- No vertex can enter an earlier strict frontier roof later in the
canonical recursion.  This is the transfinite form of the one-step
no-reentry law above. -/
theorem canonicalAccumulated_no_strictRoof_reentry
    (preferred : Stage κ → Option V)
    (hNoEnter : G.NoEdgeEnters G.source) :
    ∀ {a b : ExtendedStage κ}, a ≤ b →
      G.vertexSet (G.canonicalLadderAccumulated κ preferred b) ∩
          G.strictRoof (G.terminalFrontier
            (G.canonicalLadderAccumulated κ preferred a)) ⊆
        G.vertexSet (G.canonicalLadderAccumulated κ preferred a) := by
  let step := G.ladderSuccessorState
    (extendLadderPreference κ preferred)
  have hgeom (o : Ordinal.{u}) :
      CanonicalRecursionInvariant (G := G) step o :=
    canonicalRecursionInvariant_all hNoEnter
      (extendLadderPreference κ preferred) o
  have hmono : ∀ o : Ordinal.{u}, o ≤ κ.ord → ∀ a, a < o →
      G.vertexSet (G.ladderAccumulatedStateAux step o).1 ∩
          G.strictRoof (G.terminalFrontier
            (G.ladderAccumulatedStateAux step a).1) ⊆
        G.vertexSet (G.ladderAccumulatedStateAux step a).1 := by
    intro o
    induction o using Ordinal.limitRecOn with
    | zero =>
        intro _ a ha
        exact (not_lt_of_ge (bot_le : (0 : Ordinal.{u}) ≤ a) ha).elim
    | add_one o ih =>
        have hstate :
            G.ladderAccumulatedStateAux step (o + 1) =
              step o (G.ladderAccumulatedStateAux step o) := by
          simp [ladderAccumulatedStateAux]
        intro hobound a ha x hx
        have hao : a ≤ o := (Order.lt_add_one_iff).1 ha
        have hxStrictCurrent : x ∈ G.strictRoof (G.terminalFrontier
            (G.ladderAccumulatedStateAux step o).1) := by
          change x ∈ G.strictRoof (G.terminalFrontier
            (G.canonicalLadderAccumulated κ preferred ⟨o, ?_⟩))
          · exact canonicalAccumulated_strictRoof_mono preferred hNoEnter
              (show (⟨a, le_trans (le_of_lt ha) hobound⟩ :
                ExtendedStage κ) ≤ ⟨o, ?_⟩ from hao) hx.2
          · exact (lt_add_one o).le.trans hobound
        have hxCurrent : x ∈
            G.vertexSet (G.ladderAccumulatedStateAux step o).1 := by
          rw [hstate] at hx
          exact G.vertexSet_ladderSuccessorState_inter_strictRoof_subset
            (extendLadderPreference κ preferred) o _
              ⟨hx.1, hxStrictCurrent⟩
        rcases hao.lt_or_eq with hao | rfl
        · exact ih ((lt_add_one o).le.trans hobound)
              a hao ⟨hxCurrent, hx.2⟩
        · exact hxCurrent
    | limit o ho ih =>
        have ihStructural : ∀ b, b < o →
            G.LadderRecursionInvariant step b := by
          intro b hb
          exact ⟨(hgeom b).warp, (hgeom b).grows⟩
        let hchain : G.HasMatchingLadderChain o
            (fun b _hb ↦ G.ladderAccumulatedStateAux step b) :=
          G.hasMatchingLadderChain_of_invariants step o ihStructural
        let C : G.GrowingWarpChain (Set.Iio o) := Classical.choose hchain
        letI : Nonempty (Set.Iio o) := ho.nonempty_Iio.to_subtype
        have hstage (b : Set.Iio o) :
            C.stage b =
              (G.ladderAccumulatedStateAux step b.1).1 :=
          Classical.choose_spec hchain b
        have hstate :
            (G.ladderAccumulatedStateAux step o).1 = C.limitPaths G := by
          rw [ladderAccumulatedStateAux,
            Ordinal.limitRecOn_limit _ _ _ _ ho]
          simp only [ladderLimitState]
          split
          · rfl
          · rename_i h
            exact (h hchain).elim
        intro hobound a ha x hx
        rw [hstate, C.vertexSet_limitPaths G] at hx
        obtain ⟨c, hxc⟩ := Set.mem_iUnion.1 hx.1
        rw [hstage c] at hxc
        rcases le_total a c.1 with hac | hca
        · rcases hac.lt_or_eq with hac | hac
          · exact ih c.1 c.2 (le_trans (le_of_lt c.2) hobound)
              a hac ⟨hxc, hx.2⟩
          · simpa [hac] using hxc
        · rcases hca.lt_or_eq with hca | hca
          · exact G.vertexSet_mono_of_ladderGrows
              ((hgeom a).grows c.1 hca) hxc
          · simpa [hca] using hxc
  intro a b hab x hx
  change x ∈ G.vertexSet (G.ladderAccumulatedStateAux step b.1).1 ∩
      G.strictRoof (G.terminalFrontier
        (G.ladderAccumulatedStateAux step a.1).1) at hx
  change x ∈ G.vertexSet (G.ladderAccumulatedStateAux step a.1).1
  rcases hab.lt_or_eq with hab | rfl
  · exact hmono b.1 b.2 a.1 hab hx
  · exact hx.1

end KappaLadder

end DWeb
end Erdos599
