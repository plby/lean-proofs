/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LadderRoofRecursion
import ErdosProblems.Erdos599.QuotientAssociativity

/-!
# Strict-frontier chronology for the canonical ladder

This file proves the remaining chronology invariant of the canonical
transfinite ladder.  A successor preserves the old strict roof through the
cross-roofed arrow and then through the optional singleton marker.  At a
limit, the same statement is obtained from the liminf of the terminal
frontiers after deleting the one vertex whose strict-roof membership is
being transported.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb

universe u v

variable {V : Type u} {G : DWeb V}

/-- The canonical arrow preserves the strict roof of the accumulated
terminal frontier. -/
theorem strictRoof_terminalFrontier_subset_canonicalArrow
    (hNoEnter : G.NoEdgeEnters G.source)
    (s : G.LadderAccumulationState)
    (hwarp : G.IsWarp s.1)
    (hself : G.vertexSet s.1 ⊆ G.roof (G.terminalFrontier s.1))
    (hsource : G.source ⊆ G.roof (G.terminalFrontier s.1)) :
    G.strictRoof (G.terminalFrontier s.1) ⊆
      G.strictRoof (G.terminalFrontier
        (G.arrow s.1 (G.liftedLadderRungOfState s))) := by
  let R := G.liftedLadderRungOfState s
  have hRwarp : G.IsWarp R :=
    G.isWarp_liftedLadderRungOfState' s
  have hRself : G.vertexSet R ⊆ G.roof (G.terminalFrontier R) :=
    G.liftedLadderRungOfState_self_roofing hNoEnter s
  have hRinitial : G.initialSet R ⊆
      G.essential (G.terminalFrontier s.1) :=
    G.initialSet_liftedLadderRungOfState_subset_essential s hsource
  have hEssR : G.essential (G.terminalFrontier s.1) ⊆
      G.roof (G.terminalFrontier R) :=
    G.essential_subset_roof_terminalFrontier_liftedLadderRungOfState
      hNoEnter s
  have hOldRoofR : G.roof (G.terminalFrontier s.1) ⊆
      G.roof (G.terminalFrontier R) := by
    rw [← G.roof_essential (G.terminalFrontier s.1)]
    exact G.roof_cut hEssR
  have hOldCross : G.initialSet (s.1 ∪ R) ⊆
      G.roof (G.terminalFrontier s.1) := by
    rw [G.initialSet_union]
    intro x hx
    rcases hx with hxOld | hxR
    · exact hself (G.initialSet_subset_vertexSet' s.1 hxOld)
    · exact G.essential_subset_roof _ (hRinitial hxR)
  have hRcross : G.initialSet (s.1 ∪ R) ⊆
      G.roof (G.terminalFrontier R) := by
    rw [G.initialSet_union]
    intro x hx
    rcases hx with hxOld | hxR
    · exact hOldRoofR
        (hself (G.initialSet_subset_vertexSet' s.1 hxOld))
    · exact hEssR (hRinitial hxR)
  exact G.strictRoof_terminalFrontier_subset_arrow_left_of_crossRoof
    hwarp hRwarp hOldCross hRcross

/-- One canonical successor step preserves the strict roof of the old
terminal frontier. -/
theorem strictRoof_terminalFrontier_subset_ladderSuccessorState
    (hNoEnter : G.NoEdgeEnters G.source)
    (preferred : Ordinal.{u} → Option V) (o : Ordinal.{u})
    (s : G.LadderAccumulationState)
    (hwarp : G.IsWarp s.1)
    (hself : G.vertexSet s.1 ⊆ G.roof (G.terminalFrontier s.1))
    (hsource : G.source ⊆ G.roof (G.terminalFrontier s.1)) :
    G.strictRoof (G.terminalFrontier s.1) ⊆
      G.strictRoof (G.terminalFrontier
        (G.ladderSuccessorState preferred o s).1) := by
  classical
  by_cases hs : s.2 = true
  · rw [ladderSuccessorState, dif_pos hs]
    change G.strictRoof (G.terminalFrontier s.1) ⊆
      G.strictRoof (G.terminalFrontier
        (G.arrow s.1 (G.liftedLadderRungOfState s) ∪
          G.ladderMarkerPathSetOfState (preferred o) s))
    rw [G.terminalFrontier_union]
    exact (G.strictRoof_terminalFrontier_subset_canonicalArrow
      hNoEnter s hwarp hself hsource).trans
        (G.strictRoof_subset_strictRoof_union_left _ _)
  · rw [ladderSuccessorState, dif_neg hs]

/-- Strict roofs of terminal frontiers pass from every stage of a growing
warp chain to its genuine threadwise direct limit, provided strict roofs
are monotone along the tail of the chain. -/
theorem GrowingWarpChain.strictRoof_terminalFrontier_subset_limitPaths
    {I : Type v} [LinearOrder I] [Nonempty I] [IsDirectedOrder I]
    (C : G.GrowingWarpChain I)
    (hself : ∀ i, G.vertexSet (C.stage i) ⊆
      G.roof (G.terminalFrontier (C.stage i)))
    (hstrict : ∀ ⦃i j⦄, i ≤ j →
      G.strictRoof (G.terminalFrontier (C.stage i)) ⊆
        G.strictRoof (G.terminalFrontier (C.stage j)))
    (i : I) :
    G.strictRoof (G.terminalFrontier (C.stage i)) ⊆
      G.strictRoof (G.terminalFrontier (C.limitPaths G)) := by
  intro x hx
  have hxStrict := hx
  rw [G.mem_strictRoof_iff_mem_roof_sdiff_singleton] at hx ⊢
  let Tail := Set.Ici i
  let S : Tail → Set V := fun j ↦
    G.terminalFrontier (C.stage j.1) \ {x}
  have hS : ∀ ⦃j k : Tail⦄, j ≤ k → S j ⊆ G.roof (S k) := by
    intro j k hjk y hy
    have hyRoof : y ∈ G.roof (G.terminalFrontier (C.stage k.1)) := by
      obtain ⟨p, hp, hpterm⟩ := hy.1
      obtain ⟨q, hq, hpq⟩ := C.grows hjk p hp
      exact hself k.1 ⟨q, hq,
        G.support_mono_of_extends hpq (G.terminal_mem_support hpterm)⟩
    have hxStrict : x ∈
        G.strictRoof (G.terminalFrontier (C.stage k.1)) :=
      hstrict k.2 hxStrict
    apply G.roof_cut ?_ hyRoof
    intro z hz
    by_cases hzx : z = x
    · subst z
      exact (G.mem_strictRoof_iff_mem_roof_sdiff_singleton _ _).1
        hxStrict
    · exact G.subset_roof _ ⟨hz, by simpa [hzx]⟩
  have hxUnion : x ∈ ⋃ j : Tail, G.roof (S j) := by
    exact Set.mem_iUnion.2 ⟨⟨i, le_rfl⟩, hx⟩
  have hxLiminf : x ∈ G.roof (WarpLimits.setLiminf S) :=
    G.roof_setLiminf_of_roof_chain S hS hxUnion
  have hliminf : WarpLimits.setLiminf S ⊆
      G.terminalFrontier (C.limitPaths G) \ {x} := by
    intro y hy
    have hyTail : y ∈ WarpLimits.setLiminf
        (fun j : Tail ↦ G.terminalFrontier (C.stage j.1)) :=
      WarpLimits.setLiminf_mono (fun _ ↦ Set.sdiff_subset) hy
    obtain ⟨j, hj⟩ :=
      (WarpLimits.mem_setLiminf _ y).1 hyTail
    have hyFull : y ∈ WarpLimits.setLiminf
        (fun j : I ↦ G.terminalFrontier (C.stage j)) := by
      apply (WarpLimits.mem_setLiminf _ y).2
      refine ⟨j.1, ?_⟩
      intro k hjk
      exact hj ⟨k, j.2.trans hjk⟩ hjk
    refine ⟨C.setLiminf_terminalFrontier_subset_limitPaths hyFull, ?_⟩
    obtain ⟨j, hj⟩ := (WarpLimits.mem_setLiminf S y).1 hy
    exact (hj j le_rfl).2
  exact G.roof_mono hliminf hxLiminf

namespace KappaLadder

open Ladder

variable {κ : Cardinal.{u}}

/-- The raw strict roofs of the canonical accumulated terminal frontiers
are monotone at all ordinal stages. -/
theorem canonicalAccumulated_strictRoof_mono
    (preferred : Stage κ → Option V)
    (hNoEnter : G.NoEdgeEnters G.source) :
    ∀ {a b : ExtendedStage κ}, a ≤ b →
      G.strictRoof (G.terminalFrontier
        (G.canonicalLadderAccumulated κ preferred a)) ⊆
      G.strictRoof (G.terminalFrontier
        (G.canonicalLadderAccumulated κ preferred b)) := by
  let step := G.ladderSuccessorState
    (extendLadderPreference κ preferred)
  have hgeom (o : Ordinal.{u}) :
      CanonicalRecursionInvariant (G := G) step o :=
    canonicalRecursionInvariant_all hNoEnter
      (extendLadderPreference κ preferred) o
  have hmono : ∀ o : Ordinal.{u}, ∀ b, b < o →
      G.strictRoof (G.terminalFrontier
        (G.ladderAccumulatedStateAux step b).1) ⊆
      G.strictRoof (G.terminalFrontier
        (G.ladderAccumulatedStateAux step o).1) := by
    intro o
    induction o using Ordinal.limitRecOn with
    | zero =>
        intro b hb
        exact (not_lt_of_ge (bot_le : (0 : Ordinal.{u}) ≤ b) hb).elim
    | add_one o ih =>
        have hstate :
            G.ladderAccumulatedStateAux step (o + 1) =
              step o (G.ladderAccumulatedStateAux step o) := by
          simp [ladderAccumulatedStateAux]
        have hstep :
            G.strictRoof (G.terminalFrontier
              (G.ladderAccumulatedStateAux step o).1) ⊆
            G.strictRoof (G.terminalFrontier
              (G.ladderAccumulatedStateAux step (o + 1)).1) := by
          rw [hstate]
          exact G.strictRoof_terminalFrontier_subset_ladderSuccessorState
            hNoEnter (extendLadderPreference κ preferred) o _
              (hgeom o).warp (hgeom o).selfRoof (hgeom o).sourceRoof
        intro b hb
        have hbo : b ≤ o := (Order.lt_add_one_iff).1 hb
        rcases hbo.lt_or_eq with hbo | rfl
        · exact (ih b hbo).trans hstep
        · exact hstep
    | limit o ho ih =>
        have ihStructural : ∀ b, b < o →
            G.LadderRecursionInvariant step b := by
          intro b hb
          exact ⟨(hgeom b).warp, (hgeom b).grows⟩
        let hchain : G.HasMatchingLadderChain o
            (fun b _hb ↦ G.ladderAccumulatedStateAux step b) :=
          G.hasMatchingLadderChain_of_invariants step o ihStructural
        let C : G.GrowingWarpChain (Set.Iio o) := Classical.choose hchain
        let : Nonempty (Set.Iio o) := ho.nonempty_Iio.to_subtype
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
        intro b hb
        let bi : Set.Iio o := ⟨b, hb⟩
        have hselfC : ∀ j, G.vertexSet (C.stage j) ⊆
            G.roof (G.terminalFrontier (C.stage j)) := by
          intro j
          rw [hstage j]
          exact (hgeom j.1).selfRoof
        have hstrictC : ∀ ⦃j k : Set.Iio o⦄, j ≤ k →
            G.strictRoof (G.terminalFrontier (C.stage j)) ⊆
              G.strictRoof (G.terminalFrontier (C.stage k)) := by
          intro j k hjk
          rw [hstage j, hstage k]
          rcases hjk.lt_or_eq with hjk | rfl
          · exact ih k.1 k.2 j.1 hjk
          · exact Set.Subset.rfl
        rw [← hstage bi, hstate]
        exact C.strictRoof_terminalFrontier_subset_limitPaths
          hselfC hstrictC bi
  intro a b hab
  change G.strictRoof (G.terminalFrontier
      (G.ladderAccumulatedStateAux step a.1).1) ⊆
    G.strictRoof (G.terminalFrontier
      (G.ladderAccumulatedStateAux step b.1).1)
  rcases hab.lt_or_eq with hab | hEq
  · exact hmono b.1 a.1 hab
  · subst b
    exact Set.Subset.rfl

/-- The canonical ladder satisfies the strict-frontier chronology required
by source Lemma 7.11. -/
theorem canonicalLadder_hasStrictFrontierChronology
    (preferred : Stage κ → Option V)
    (hNoEnter : G.NoEdgeEnters G.source) :
    (canonicalLadder G κ preferred).HasStrictFrontierChronology := by
  have hgeometry := canonicalLadder_geometry preferred hNoEnter
  apply (canonicalLadder G κ preferred)
    |>.hasStrictFrontierChronology_of_strictRoof_mono
      hgeometry.roofsSourceAtStages
  intro a b hab
  exact canonicalAccumulated_strictRoof_mono preferred hNoEnter hab.le

end KappaLadder
end DWeb
end Erdos599
