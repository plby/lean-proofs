/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LadderBookkeepingChoice
import ErdosProblems.Erdos599.LadderConstruction
import ErdosProblems.Erdos599.LadderFrontierInvariants
import ErdosProblems.Erdos599.LadderMarkerDisjoint
import ErdosProblems.Erdos599.LadderSuccessorSelfRoof

/-!
# Roof invariants for the canonical ladder recursion

This file packages the simultaneous transfinite induction which supplies the
warp, growth, self-roofing, and source-roofing invariants of the canonical
ladder.  It is kept below both the legal-ladder assembly and the strict
chronology proof so those two modules can share the same checked induction
without an import cycle.
-/

noncomputable section

open Cardinal
open Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

universe u

variable {V : Type u} {G : DWeb V} {κ : Cardinal.{u}}

/-- The strengthened invariant needed to run the canonical ordinal
recursion.  Besides the warp/growth data used by the direct-limit
constructor, it carries the two roofing properties needed to justify the
next marker and to pass source separation through limits. -/
structure CanonicalRecursionInvariant
    (step : Ordinal.{u} → G.LadderAccumulationState →
      G.LadderAccumulationState)
    (o : Ordinal.{u}) : Prop where
  warp : G.IsWarp (G.ladderAccumulatedStateAux step o).1
  grows : ∀ b, b < o →
    G.LadderGrows (G.ladderAccumulatedStateAux step b).1
      (G.ladderAccumulatedStateAux step o).1
  selfRoof : G.vertexSet (G.ladderAccumulatedStateAux step o).1 ⊆
    G.roof (G.terminalFrontier
      (G.ladderAccumulatedStateAux step o).1)
  sourceRoof : G.source ⊆ G.roof (G.terminalFrontier
    (G.ladderAccumulatedStateAux step o).1)

/-- A successor rule preserving the four local invariants gives a genuine
threadwise ordinal recursion with those invariants. The limit proof is
independent of the marker-selection rule. -/
theorem recursionInvariant_all_of_step
    (step : Ordinal.{u} → G.LadderAccumulationState → G.LadderAccumulationState)
    (hwarpStep : ∀ (o : Ordinal.{u}) (s : G.LadderAccumulationState), G.IsWarp s.1 →
      G.vertexSet s.1 ⊆ G.roof (G.terminalFrontier s.1) →
      G.source ⊆ G.roof (G.terminalFrontier s.1) → G.IsWarp (step o s).1)
    (hgrowsStep : ∀ (o : Ordinal.{u}) (s : G.LadderAccumulationState),
      G.LadderGrows s.1 (step o s).1)
    (hroofStep : ∀ (o : Ordinal.{u}) (s : G.LadderAccumulationState), G.IsWarp s.1 →
      G.vertexSet s.1 ⊆ G.roof (G.terminalFrontier s.1) →
      G.source ⊆ G.roof (G.terminalFrontier s.1) →
      (G.vertexSet (step o s).1 ⊆ G.roof (G.terminalFrontier (step o s).1)) ∧
      (G.source ⊆ G.roof (G.terminalFrontier (step o s).1))) :
    ∀ o, CanonicalRecursionInvariant (G := G) step o := by
  intro o
  induction o using Ordinal.limitRecOn with
  | zero =>
      refine
        { warp := ?_
          grows := ?_
          selfRoof := ?_
          sourceRoof := ?_ }
      · simpa [ladderAccumulatedStateAux] using G.isWarp_trivialWave
      · intro b hb
        exact (not_lt_of_ge (bot_le : (0 : Ordinal.{u}) ≤ b) hb).elim
      · simpa [ladderAccumulatedStateAux] using
          G.isWave_trivialWave.self_roofing
      · simpa [ladderAccumulatedStateAux] using
          G.isWave_trivialWave.2.2
  | add_one o ih =>
      have hstate :
          G.ladderAccumulatedStateAux step (o + 1) =
            step o (G.ladderAccumulatedStateAux step o) := by
        simp [ladderAccumulatedStateAux]
      have hroof := hroofStep o (G.ladderAccumulatedStateAux step o)
        ih.warp ih.selfRoof ih.sourceRoof
      refine
        { warp := ?_
          grows := ?_
          selfRoof := ?_
          sourceRoof := ?_ }
      · rw [hstate]
        exact hwarpStep o _ ih.warp ih.selfRoof ih.sourceRoof
      · intro b hb
        rw [hstate]
        have hbo : b ≤ o := (Order.lt_add_one_iff).1 hb
        rcases hbo.lt_or_eq with hbo | heq
        · exact LadderGrows.trans (G := G) (ih.grows b hbo)
            (hgrowsStep o _)
        · subst b
          exact hgrowsStep o _
      · rw [hstate]
        exact hroof.1
      · rw [hstate]
        exact hroof.2
  | limit o ho ih =>
      have ihStructural : ∀ b, b < o →
          G.LadderRecursionInvariant step b := by
        intro b hb
        exact ⟨(ih b hb).warp, (ih b hb).grows⟩
      let hchain : G.HasMatchingLadderChain o
          (fun b _hb ↦ G.ladderAccumulatedStateAux step b) :=
        G.hasMatchingLadderChain_of_invariants step o ihStructural
      let C : G.GrowingWarpChain (Set.Iio o) := Classical.choose hchain
      have hstate :
          (G.ladderAccumulatedStateAux step o).1 = C.limitPaths G := by
        rw [ladderAccumulatedStateAux,
          Ordinal.limitRecOn_limit _ _ _ _ ho]
        simp only [ladderLimitState]
        split
        · rfl
        · rename_i h
          exact (h hchain).elim
      let : Nonempty (Set.Iio o) := ho.nonempty_Iio.to_subtype
      have hstage (b : Set.Iio o) :
          C.stage b =
            (G.ladderAccumulatedStateAux step b.1).1 :=
        Classical.choose_spec hchain b
      refine
        { warp := ?_
          grows := ?_
          selfRoof := ?_
          sourceRoof := ?_ }
      · rw [hstate]
        exact C.isWarp_limitPaths G
      · intro b hb
        rw [hstate]
        let bi : Set.Iio o := ⟨b, hb⟩
        intro p hp
        have hpC : p ∈ C.stage bi := by
          rw [hstage bi]
          exact hp
        exact C.grows_limitPaths G bi p hpC
      · rw [hstate]
        apply C.vertexSet_limitPaths_subset_roof_terminalFrontier
        intro b
        rw [hstage b]
        exact (ih b.1 b.2).selfRoof
      · rw [hstate]
        apply C.source_subset_roof_terminalFrontier_limitPaths
        · intro b
          rw [hstage b]
          exact (ih b.1 b.2).sourceRoof
        · intro b
          rw [hstage b]
          exact (ih b.1 b.2).selfRoof

/-- The historical canonical rule is an instance of the general invariant
theorem. Its previously proved successor and limit properties are retained. -/
theorem canonicalRecursionInvariant_all
    (hNoEnter : G.NoEdgeEnters G.source)
    (preferred : Ordinal.{u} → Option V) :
    ∀ o, CanonicalRecursionInvariant (G := G)
      (G.ladderSuccessorState preferred) o := by
  apply recursionInvariant_all_of_step (G.ladderSuccessorState preferred)
  · intro o s hwarp hself hsource
    exact G.isWarp_ladderSuccessorState_of_roofs preferred o s hwarp hsource hself
  · exact G.ladderSuccessorState_grows preferred
  · intro o s hwarp hself hsource
    exact G.ladderSuccessorState_roof_invariants hNoEnter preferred o s
      hwarp hself hsource

/-- The canonical core with the canonical ray-preferring bookkeeping. -/
noncomputable abbrev canonicalLadder
    (G : DWeb V) (κ : Cardinal.{u})
    (preferred : Ladder.Stage κ → Option V) : G.KappaLadder κ :=
  (G.canonicalLadderCore κ preferred).withValidBookkeeping

/-- The geometric output of the strengthened ordinal induction. -/
structure CanonicalLadderGeometry (L : G.KappaLadder κ) : Prop where
  warpStages : L.HasWarpStages
  limitStages : L.HasLimitStages
  roofsSourceAtStages : L.RoofsSourceAtStages
  selfRoofing : ∀ a : Ladder.ExtendedStage κ,
    G.vertexSet (L.accumulated a) ⊆
      G.roof (G.terminalFrontier (L.accumulated a))
  grows : ∀ {a b : Ladder.ExtendedStage κ}, a ≤ b →
    G.LadderGrows (L.accumulated a) (L.accumulated b)
  frontierChronology : L.HasFrontierChronology

/-- Warp stages, genuine direct limits, source separation, and frontier
chronology for the bookkeeping-installed canonical ladder. -/
theorem canonicalLadder_geometry
    (preferred : Ladder.Stage κ → Option V)
    (hNoEnter : G.NoEdgeEnters G.source) :
    CanonicalLadderGeometry (canonicalLadder G κ preferred) := by
  let step := G.ladderSuccessorState
    (extendLadderPreference κ preferred)
  have hinv (o : Ordinal.{u}) :
      CanonicalRecursionInvariant (G := G) step o :=
    canonicalRecursionInvariant_all hNoEnter
      (extendLadderPreference κ preferred) o
  have hwarp : (canonicalLadder G κ preferred).HasWarpStages := by
    intro a
    exact (hinv a.1).warp
  have hlimit : (canonicalLadder G κ preferred).HasLimitStages := by
    intro a ha
    apply G.exists_ladderLimitChain κ step a ha
    apply G.hasMatchingLadderChain_of_invariants step a.1
    intro b hb
    exact ⟨(hinv b).warp, (hinv b).grows⟩
  have hroof :
      (canonicalLadder G κ preferred).RoofsSourceAtStages := by
    intro a
    exact (hinv a.1).sourceRoof
  have hself : ∀ a : Ladder.ExtendedStage κ,
      G.vertexSet ((canonicalLadder G κ preferred).accumulated a) ⊆
        G.roof (G.terminalFrontier
          ((canonicalLadder G κ preferred).accumulated a)) := by
    intro a
    exact (hinv a.1).selfRoof
  have hgrows : ∀ {a b : Ladder.ExtendedStage κ}, a ≤ b →
      G.LadderGrows
        ((canonicalLadder G κ preferred).accumulated a)
        ((canonicalLadder G κ preferred).accumulated b) := by
    intro a b hab
    rcases hab.lt_or_eq with hab | rfl
    · exact (hinv b.1).grows a.1 hab
    · exact G.ladderGrows_refl _
  have hchronology :
      (canonicalLadder G κ preferred).HasFrontierChronology := by
    let L := canonicalLadder G κ preferred
    apply L.hasFrontierChronology_of_grows_of_selfRoofing hroof
    · intro a b hab
      exact hgrows hab.le
    · intro b
      exact hself (Ladder.Stage.toExtended b)
  exact
    { warpStages := hwarp
      limitStages := hlimit
      roofsSourceAtStages := hroof
      selfRoofing := hself
      grows := hgrows
      frontierChronology := hchronology }

end KappaLadder
end DWeb
end Erdos599
